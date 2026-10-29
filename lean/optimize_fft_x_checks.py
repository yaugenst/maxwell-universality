#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Prepare import-light X checks, then switch only uncompiled proof wrappers.

Run --prepare while production continues. Run --apply only at a coordinated
worker boundary; it preserves all compiled scalar completions and modifies
only the proof of their existing public interval-containment statements.
"""
import argparse
import contextlib
import io
import json
import re
from pathlib import Path

import generate_fft_raw_prototype as raw

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/fft_stage_proposals"
OLD = "Maxwell.Certificate.FFTWitness."
RAW = "Maxwell.Certificate.FFTRawWitness."


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--label", choices=["Lower", "Upper", "Both"], default="Both")
    parser.add_argument("--first-column", type=int, default=0)
    args = parser.parse_args()
    assert args.prepare != args.apply, "Choose exactly one phase"
    path = EVIDENCE / "raw_x_prepared.json"
    prepared = json.loads(path.read_text()) if path.exists() else []
    if args.prepare:
        labels = ["Lower", "Upper"] if args.label == "Both" else [args.label]
        count = 0
        for label in labels:
            for column in range(args.first_column, 28):
                for forward in [False, True]:
                    for direction in range(3):
                        prefix = f"{label}{'Forward' if forward else ''}D{direction}C{column:02}"
                        output = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/FFTWitness" / (prefix + "ListComplete.olean")
                        checked_x = output.with_name(prefix + "ListCheckXBlocks.olean")
                        if output.exists() or checked_x.exists():
                            continue
                        argv = ["--label", label, "--column", str(column), "--direction", str(direction), "--only-x"]
                        if forward:
                            argv.append("--forward")
                        with contextlib.redirect_stdout(io.StringIO()):
                            raw.main(argv)
                        prepared.append(prefix)
                        count += 1
                print(f"Prepared {label} column {column:02}.", flush=True)
        path.write_text(json.dumps(sorted(set(prepared)), indent=2) + "\n")
        print(f"Prepared {count} raw X stages; production sources and manifests unchanged.")
        return

    replacements_path = EVIDENCE / "raw_x_replacements.json"
    replaced = json.loads(replacements_path.read_text()) if replacements_path.exists() else []
    changed = []
    pattern = re.compile(r"  · apply DyadicFFT\.axisXCheck_of_rows\n.*?(?=\n  · apply|\n/--)", re.S)
    for prefix in prepared:
        output = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/FFTWitness" / (prefix + "ListComplete.olean")
        checked_x = output.with_name(prefix + "ListCheckXBlocks.olean")
        if output.exists() or checked_x.exists() or prefix in replaced:
            continue
        source = ROOT / "Maxwell/Certificate/FFTWitness" / (prefix + "ListComplete.lean")
        old = source.read_text()
        new = old.replace("import " + OLD + prefix + "ListCheckXBlocks", "import " + RAW + prefix + "RawXSound")
        new, count = pattern.subn("  · exact FFTRawWitness." + prefix + "RawX_accepted\n", new)
        assert count == 1, (prefix, count)
        source.write_text(new)
        changed.append(prefix)
    replaced = sorted(set(replaced + changed))
    replacements_path.write_text(json.dumps(replaced, indent=2) + "\n")
    print(f"Switched {len(changed)} uncompiled scalar X-stage proofs; {len(replaced)} total replacements.")


if __name__ == "__main__":
    main()
