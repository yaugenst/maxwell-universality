#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Freshly compile and replay the scoped continuum analytic proof closure."""

from __future__ import annotations

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
AUDIT = "ContinuumAnalysisAudit"
BUILD = ROOT / ".lake/continuum-analysis-check/lib/lean"
EVIDENCE = ROOT / "evidence/continuum-analysis"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def source(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def imports(module: str) -> set[str]:
    result: set[str] = set()
    for line in source(module).read_text().splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
        if match:
            result.update(name for name in match[1].split() if name.startswith("Maxwell."))
    return result


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    if hasattr(os, "sched_getaffinity"):
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    graph: dict[str, set[str]] = {}
    pending = [AUDIT]
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        graph[module] = imports(module)
        pending.extend(graph[module])
    tracked = [source(module) for module in graph]
    tracked.extend(ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", Path(__file__).name))
    before = {str(path.relative_to(ROOT)): sha256(path) for path in tracked}
    environment = os.environ.copy()
    lean_path = subprocess.check_output(
        [lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    environment["LEAN_PATH"] = str(BUILD) + os.pathsep + lean_path
    binaries = subprocess.check_output(
        [lake, "env", "which", "lean", "leanchecker", "leanexport"],
        cwd=ROOT, text=True).splitlines()
    lean, leanchecker, leanexport = binaries
    environment["PATH"] = str(Path(lean).parent) + os.pathsep + environment.get("PATH", "")
    checks: list[dict[str, object]] = []
    start = time.monotonic()
    receipt: dict[str, object] = {
        "status": "running",
        "scope": "imported continuum analytic components; not the complete Maxwell reduction",
        "root": AUDIT,
        "modules": sorted(graph),
        "source_sha256": before,
        "checks": checks,
    }
    receipt_path = EVIDENCE / "validation.json"

    def save() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    def run(command: list[str], log_name: str, output: Path | None = None) -> str:
        began = time.monotonic()
        log_path = EVIDENCE / log_name
        if output is None:
            with log_path.open("w") as log:
                result = subprocess.run(command, cwd=ROOT, env=environment,
                    text=True, stdout=log, stderr=subprocess.STDOUT, check=False)
        else:
            with output.open("w") as destination, log_path.open("w") as log:
                result = subprocess.run(command, cwd=ROOT, env=environment,
                    text=True, stdout=destination, stderr=log, check=False)
        checks.append({"command": command, "log": log_name, "exit_code": result.returncode,
                       "seconds": round(time.monotonic() - began, 3)})
        save()
        print(f"{log_name}: exit {result.returncode}", flush=True)
        if result.returncode:
            raise RuntimeError(f"{log_name} failed; see {log_path}")
        return log_path.read_text()

    save()
    try:
        receipt["lean_version"] = run([lean, "--version"], "version.log").strip()
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        revisions: dict[str, str] = {}
        for package in manifest["packages"]:
            directory = ROOT / manifest["packagesDir"] / package["name"]
            revision = subprocess.check_output(
                ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
            changes = subprocess.check_output(
                ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
                text=True)
            if revision != package["rev"] or changes.strip():
                raise RuntimeError(f"Dependency does not match pinned source: {package['name']}")
            revisions[package["name"]] = revision
        receipt["dependency_revisions"] = revisions
        for module in TopologicalSorter(graph).static_order():
            output = BUILD / (module.replace(".", "/") + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            run([lean, "-j1", "-M6000", "-DautoImplicit=false",
                 "-DwarningAsError=true", "-o", str(output), str(source(module))],
                f"build-{module}.log")
        audit = (EVIDENCE / f"build-{AUDIT}.log").read_text()
        imported = set(re.findall(r"^CONTINUUM_MODULE\t(\S+)$", audit, re.M))
        if imported != set(graph) - {AUDIT}:
            raise RuntimeError("Elaborated and source import inventories differ")
        declared_axioms = re.findall(r"^CONTINUUM_AXIOM\t(\S+)$", audit, re.M)
        if declared_axioms:
            raise RuntimeError(f"Custom project axioms: {declared_axioms}")
        reports = re.findall(r"^CONTINUUM_THEOREM\t([^\t\n]+)\t([^\n]*)$", audit, re.M)
        theorems = [name for name, _ in reports]
        if not theorems or len(theorems) != len(set(theorems)):
            raise RuntimeError("Empty or repeated theorem inventory")
        axioms: dict[str, list[str]] = {}
        for name, names in reports:
            used = {part for part in names.split(",") if part}
            if not used <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unaccepted axioms for {name}: {used}")
            axioms[name] = sorted(used)
        receipt["theorem_axioms"] = axioms
        for module in sorted(graph):
            run([leanchecker, "--verbose", module], f"recheck-{module}.log")
        export = EVIDENCE / "theorems.ndjson"
        run([leanexport, AUDIT, "--", *theorems], "export.log", output=export)
        run([lake, "check", f"--from-export={export}"], "transitive-check.log")
        after = {str(path.relative_to(ROOT)): sha256(path) for path in tracked}
        if after != before:
            raise RuntimeError("An imported proof source changed during verification")
        receipt.update({
            "status": "passed",
            "theorem_count": len(theorems),
            "seconds": round(time.monotonic() - start, 3),
            "export": {"sha256": sha256(export), "bytes": export.stat().st_size},
            "kernel_recheck_boundary": "All inventoried component proofs and their transitive "
                "proof/type dependencies replayed from an empty environment by the pinned Lean "
                "default kernel. This is not an independently implemented kernel or a proof "
                "of the complete continuum reduction theorem.",
        })
        save()
        print(f"Validated {len(theorems)} scoped component theorems; {receipt_path}", flush=True)
    except BaseException as error:
        receipt.update({"status": "failed", "error": str(error),
                        "seconds": round(time.monotonic() - start, 3)})
        save()
        raise


if __name__ == "__main__":
    main()
