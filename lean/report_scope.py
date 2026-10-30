#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Report proof import scopes and their recorded source-hash coverage.

This reads source files and existing receipts. It neither runs Lean nor
replaces the proof verifiers. Paths in the output are relative to lean/.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def closure(roots: list[str]) -> tuple[set[str], list[str]]:
    modules: set[str] = set()
    missing: list[str] = []
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        modules.add(module)
        path = module_path(module)
        if not path.is_file():
            missing.append(str(path.relative_to(ROOT)))
            continue
        for line in path.read_text().splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
            if match:
                pending.extend(name for name in match[1].split()
                               if name == "Maxwell" or name.startswith("Maxwell."))
    return modules, sorted(missing)


def receipt_report(path: Path, modules: set[str], manifest: dict) -> dict:
    if not path.is_file():
        return {"path": str(path.relative_to(ROOT)), "available": False}
    receipt = json.loads(path.read_text())
    hashes = receipt.get("source_sha256", {})
    changed: list[str] = []
    missing: list[str] = []
    transformed: list[str] = []
    matching = 0
    for name, expected in hashes.items():
        source = ROOT / name
        if not source.is_file():
            missing.append(name)
            continue
        actual = digest(source)
        if actual == expected:
            matching += 1
            continue
        record = manifest.get("lean/" + name, {})
        if record.get("source_sha256") == expected and record.get("sha256") == actual:
            transformed.append(name)
        else:
            changed.append(name)
    unhashed = sorted(str(module_path(module).relative_to(ROOT)) for module in modules
                      if str(module_path(module).relative_to(ROOT)) not in hashes)
    inventory_matches = set(receipt.get("modules", [])) == modules
    return {
        "path": str(path.relative_to(ROOT)),
        "available": True,
        "recorded_status": receipt.get("status"),
        "recorded_scope": receipt.get("scope"),
        "recorded_theorem_count": receipt.get("theorem_count"),
        "recorded_seconds": receipt.get("seconds"),
        "recorded_modules": len(receipt.get("modules", [])),
        "current_module_inventory_matches": inventory_matches,
        "matching_source_files": matching,
        "changed_source_files": sorted(changed),
        "missing_source_files": sorted(missing),
        "distribution_transformed_files": sorted(transformed),
        "current_modules_without_recorded_hash": unhashed,
        "recorded_source_hashes_match_current_files": bool(hashes) and
            not (changed or missing or transformed or unhashed) and inventory_matches,
        "interpretation": "A source hash match binds a historical receipt to those bytes; "
            "this report does not perform a new proof check. Distribution transformations "
            "are traced through data/manifest.json and are not byte-identical replay evidence.",
    }


def main() -> None:
    scopes = json.loads((ROOT / "proof-scopes.json").read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope", choices=sorted(scopes), nargs="?",
                        help="report one scope; by default report all")
    args = parser.parse_args()
    manifest_path = ROOT.parent / "data/manifest.json"
    manifest = json.loads(manifest_path.read_text())["files"] if manifest_path.is_file() else {}
    all_project_modules = {"Maxwell", *(str(path.relative_to(ROOT).with_suffix(""))
        .replace("/", ".") for path in (ROOT / "Maxwell").rglob("*.lean"))}
    output = {}
    for name in ([args.scope] if args.scope else scopes):
        scope = scopes[name]
        modules, missing = closure(scope["roots"])
        entry = {**scope, "current_module_count": len(modules),
                 "missing_module_sources": missing,
                 "project_module_count_outside_roots": len(all_project_modules - modules)}
        entry["receipts"] = [receipt_report(ROOT / path, modules, manifest)
                             for path in scope["receipts"]]
        output[name] = entry
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
