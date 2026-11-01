#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Strict incremental compilation of selected local Lean dependency closures.

This is a development check, not the complete theorem export/kernel replay.
Unchanged dependencies may use the recorded continuum-refresh build; changed
modules and their importers are rebuilt in a separate directory.
"""

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
WORK = ROOT / ".lake/continuum-work"
BUILD = WORK / "lib/lean"
BASE = ROOT / ".lake/proof-refresh/lib/lean"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-build", action="append", type=Path, default=[],
                        help="Reuse a same-session strict build after checking source closure and artifact hashes")
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    for module in args.modules:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module):
            parser.error(f"Invalid module name: {module}")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if hasattr(os, "sched_getaffinity"):
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    graph: dict[str, set[str]] = {}
    pending = list(args.modules)
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        deps: set[str] = set()
        for line in source(module).read_text().splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
            if match:
                deps.update(name for name in match[1].split() if name.startswith("Maxwell."))
        graph[module] = deps
        pending.extend(sorted(deps))

    baseline = json.loads((ROOT / "checks/continuum-refresh.json").read_text())
    hashes = baseline["source_sha256"]
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        if digest(ROOT / name) != hashes[name]:
            raise RuntimeError(f"Recorded cache configuration differs: {name}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        directory = ROOT / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        changed = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
        if revision != package["rev"] or changed.strip():
            raise RuntimeError(f"Dependency differs from pinned sources: {package['name']}")

    BUILD.mkdir(parents=True, exist_ok=True)
    logs = WORK / "logs"
    logs.mkdir(exist_ok=True)
    environment = os.environ.copy()
    lean_path = subprocess.check_output(
        [lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    environment["LEAN_PATH"] = os.pathsep.join((str(BUILD), str(BASE), lean_path))
    lean = subprocess.check_output([lake, "env", "which", "lean"], cwd=ROOT, text=True).strip()
    (WORK / "lean-path.txt").write_text(environment["LEAN_PATH"] + "\n")
    receipt_path = WORK / "compilation.json"
    previous = json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
    entries = previous.get("modules", {})
    peers = [(directory, json.loads((directory / "compilation.json").read_text()).get("modules", {}))
             for directory in args.reuse_build]
    receipt = {"scope": "incremental strict compilation; no complete kernel replay",
               "roots": args.modules, "status": "running", "modules": entries}
    baseline_ok: dict[str, bool] = {}
    fingerprints: dict[str, str] = {}
    rebuilt = 0
    try:
        for module in TopologicalSorter(graph).static_order():
            path = source(module)
            sha = digest(path)
            relative = path.relative_to(ROOT)
            key = json.dumps([sha, sorted((dep, fingerprints[dep]) for dep in graph[module])])
            fingerprint = hashlib.sha256(key.encode()).hexdigest()
            fingerprints[module] = fingerprint
            baseline_ok[module] = (hashes.get(str(relative)) == sha
                and all(baseline_ok[dep] for dep in graph[module])
                and (BASE / relative.with_suffix(".olean")).is_file())
            output = BUILD / relative.with_suffix(".olean")
            entry = entries.get(module, {})
            if (entry.get("fingerprint") == fingerprint and output.is_file()
                    and entry.get("olean_sha256") == digest(output)):
                continue
            reused = False
            for directory, peer_entries in peers:
                peer_entry = peer_entries.get(module, {})
                cached = directory / "lib/lean" / relative.with_suffix(".olean")
                if (peer_entry.get("fingerprint") != fingerprint or not cached.is_file()
                        or peer_entry.get("olean_sha256") != digest(cached)):
                    continue
                output.parent.mkdir(parents=True, exist_ok=True)
                for artifact in cached.parent.glob(cached.name + "*"):
                    target = output.parent / artifact.name
                    if target.is_symlink():
                        target.unlink()
                    shutil.copy2(artifact, target)
                if digest(output) != peer_entry["olean_sha256"]:
                    raise RuntimeError(f"Reused artifact changed during copy: {module}")
                entries[module] = {**peer_entry, "reused_from": str(directory)}
                reused = True
                break
            if reused:
                continue
            if baseline_ok[module] and (not output.exists() or output.is_symlink()):
                output.parent.mkdir(parents=True, exist_ok=True)
                cached = BASE / relative.with_suffix(".olean")
                for artifact in cached.parent.glob(cached.name + "*"):
                    link = output.parent / artifact.name
                    if not link.exists():
                        link.symlink_to(artifact)
                continue
            output.parent.mkdir(parents=True, exist_ok=True)
            for artifact in output.parent.glob(output.name + "*"):
                if artifact.is_symlink():
                    artifact.unlink()
            command = [lean, "-j1", "-M6000", "-DautoImplicit=false",
                       "-DwarningAsError=true", "-o", str(output), str(path)]
            started = time.monotonic()
            print(f"CHECK {module}", flush=True)
            with (logs / f"{module}.log").open("w") as log:
                result = subprocess.run(command, cwd=ROOT, env=environment,
                                        stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                output.unlink(missing_ok=True)
                raise RuntimeError(f"{module}: exit {result.returncode}; see {logs / (module + '.log')}")
            if digest(path) != sha:
                output.unlink(missing_ok=True)
                raise RuntimeError(f"Source changed during compilation: {module}")
            entries[module] = {"source_sha256": sha, "fingerprint": fingerprint,
                               "olean_sha256": digest(output),
                               "seconds": round(time.monotonic() - started, 3)}
            receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
            rebuilt += 1
        receipt.update(status="passed", closure_modules=len(graph), rebuilt=rebuilt)
        print(f"PASS {len(graph)} modules in closure; {rebuilt} rebuilt", flush=True)
    except BaseException as error:
        receipt.update(status="failed", error=str(error))
        raise
    finally:
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
