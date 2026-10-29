#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Rebuild local proofs, audit axioms, and replay their transitive proof export."""

from __future__ import annotations

import argparse
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FINAL_THEOREM = "Maxwell.Realization.quantitative_realization"


def project_sources() -> list[Path]:
    return [ROOT / "Maxwell.lean", *sorted((ROOT / "Maxwell").rglob("*.lean"))]


def source_hashes() -> dict[str, str]:
    paths = project_sources() + [ROOT / name for name in
        ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "Audit.lean", "verify.py"]]
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths}


def local_imports(module: str) -> set[str]:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise RuntimeError(f"Missing local module source: {module}")
    imports: set[str] = set()
    for line in path.read_text().splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
        if match:
            imports.update(name for name in match[1].split()
                           if name == "Maxwell" or name.startswith("Maxwell."))
    return imports


def import_closure() -> set[str]:
    """Require the checked root to include every shipped proof source."""
    pending = ["Maxwell"]
    modules: set[str] = set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        modules.add(module)
        pending.extend(local_imports(module))
    expected = {str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
                for path in project_sources()}
    if modules != expected:
        raise RuntimeError("Proof sources disconnected from Maxwell.lean: " +
                           ", ".join(sorted(expected - modules)))
    return modules


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true",
                        help="remove only local build outputs before checking; use with no active builds")
    args = parser.parse_args()
    modules = import_closure()
    before_hashes = source_hashes()
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / "validation.json").unlink(missing_ok=True)
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    # All descendants share at most two CPUs, including Lake's build workers.
    if hasattr(os, "sched_getaffinity"):
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    start = time.monotonic()
    checks: list[dict[str, object]] = []

    def run(args: list[str], log: str, output: Path | None = None) -> str:
        began = time.monotonic()
        if output is None:
            completed = subprocess.run(
                args, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                check=False,
            )
            log_text = completed.stdout
        else:
            with output.open("w") as destination:
                completed = subprocess.run(
                    args, cwd=ROOT, text=True, stdout=destination, stderr=subprocess.PIPE,
                    check=False,
                )
            log_text = completed.stderr
        (EVIDENCE / log).write_text(log_text)
        checks.append({"command": args, "log": log, "exit_code": completed.returncode,
                       "seconds": round(time.monotonic() - began, 3)})
        print(f"{log}: exit {completed.returncode}", flush=True)
        if completed.returncode:
            raise RuntimeError(f"{log} failed; see {EVIDENCE / log}")
        return log_text

    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    version = run([lake, "env", "lean", "--version"], "lean-version.log").strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies: dict[str, str] = {}
    for dependency in manifest["packages"]:
        directory = ROOT / manifest["packagesDir"] / dependency["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != dependency["rev"]:
            raise RuntimeError(f"{dependency['name']}: dependency revision differs from lock file")
        changes = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True
        )
        if changes.strip():
            raise RuntimeError(f"{dependency['name']}: tracked dependency sources were modified")
        dependencies[dependency["name"]] = revision

    # Explicit only: other agents may be compiling scoped modules concurrently.
    if args.clean and (ROOT / ".lake/build").exists():
        shutil.rmtree(ROOT / ".lake/build")
    # Explicit topological compilation keeps a single compiler process active.
    # Affinity alone would not prevent Lake from scheduling many memory-heavy
    # independent certificate chunks at once, especially with missing traces.
    order = TopologicalSorter({module: local_imports(module)
                               for module in sorted(modules)}).static_order()
    for module in order:
        relative = module.replace(".", "/")
        output = ROOT / ".lake/build/lib/lean" / f"{relative}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        # Main's concrete finite-machine base-case proof was measured at
        # 3.73 GiB; keep the single compiler bounded above that observed peak.
        run([lake, "env", "lean", "-j1", "-M4500", "-DautoImplicit=false",
             "-DwarningAsError=true", f"{relative}.lean", "-o", str(output)],
            f"build-{module.lower().replace('.', '-')}.log")
    audit = run([lake, "env", "lean", "-j1", "-DwarningAsError=true", "Audit.lean"],
                "axioms.log")
    imported = set(re.findall(r"^MAXWELL_MODULE\t(\S+)$", audit, re.M))
    if imported != modules:
        raise RuntimeError("Elaborated module inventory differs from recursive source import closure")
    local_axioms = re.findall(r"^MAXWELL_AXIOM\t(\S+)$", audit, re.M)
    if local_axioms:
        raise RuntimeError(f"Project declares custom axioms: {local_axioms}")
    reports = re.findall(r"^MAXWELL_THEOREM\t([^\t\n]+)\t([^\n]*)$", audit, re.M)
    theorems = [name for name, _ in reports]
    if not theorems or len(theorems) != len(set(theorems)):
        raise RuntimeError("Empty or duplicate theorem inventory")
    if FINAL_THEOREM not in theorems:
        raise RuntimeError(f"Full realization is not proved: missing theorem {FINAL_THEOREM}")
    axioms: dict[str, list[str]] = {}
    for name, names in reports:
        used = {part.strip() for part in names.split(",") if part.strip()}
        if not used <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unaccepted axiom dependencies for {name}: {used}")
        axioms[name] = sorted(used)

    gate = ROOT / ".lake/ReleaseGate.lean"
    gate.write_text("import Maxwell\nexample (p : Maxwell.Source.Parameters) :\n"
                    "    Maxwell.Realization.QuantitativeRealization p :=\n"
                    f"  {FINAL_THEOREM} p\n")
    run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(gate)],
        "release-type-gate.log")

    for module in sorted(modules):
        run([lake, "env", "leanchecker", "--verbose", module],
            f"recheck-{module.lower().replace('.', '-')}.log")

    export = ROOT / ".lake/theorems.ndjson"
    run([lake, "env", "leanexport", "Maxwell", "--", *theorems], "export.log", output=export)
    run([lake, "check", "--from-export=.lake/theorems.ndjson"], "transitive-check.log")

    after_hashes = source_hashes()
    if after_hashes != before_hashes:
        raise RuntimeError("Project sources changed during verification; evidence would be stale")
    record = {
        "status": "passed", "scope": "full project and exact quantitative realization theorem",
        "clean_build": args.clean, "modules": sorted(modules), "final_theorem": FINAL_THEOREM,
        "toolchain": toolchain, "lean_version": version, "dependencies": dependencies,
        "checks": checks, "axioms": axioms,
        "source_sha256": after_hashes,
        "seconds": round(time.monotonic() - start, 3),
        "transitive_export": {"sha256": hashlib.sha256(export.read_bytes()).hexdigest(),
                              "bytes": export.stat().st_size, "theorem_roots": theorems},
        "kernel_recheck_boundary": (
            f"All {len(theorems)} project theorem roots and their proof/type dependencies replayed from an empty "
            "environment by the pinned Lean default kernel, with the standard three-axiom whitelist. "
            "This does not use an independently implemented kernel."
        ),
    }
    (EVIDENCE / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Validated {len(theorems)} theorems; evidence: {EVIDENCE}")


if __name__ == "__main__":
    main()
