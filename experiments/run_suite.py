#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Sequential GPU experiment suite; run inside the dedicated environment.

uv run --no-project --python .venv/bin/python --no-sync python run_suite.py --output results/gpu_suite
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time


CASES = [
    ("gadget_o8_h025", ["gadget", "--h", ".25"]),
    ("gadget_o8_h02", ["gadget", "--h", ".2"]),
    ("triple_o8_h0167", ["triple", "--h", "0.16666666666666666"]),
    ("triple_o6_h02", ["triple", "--h", ".2", "--order", "6"]),
    ("buffer_z_h02", ["triple", "--h", ".2", "--lengths", "6", "6", "14"]),
    ("buffer_xy_h02", ["triple", "--h", ".2", "--lengths", "8", "8", "10"]),
    ("separation4_h02", ["gadget", "--h", ".2", "--separation", "4", "--lengths", "6", "6", "14"]),
    ("radius2_h025", ["gadget", "--h", ".25", "--radius", "2", "--separation", "4",
                      "--lengths", "8", "8", "14", "--strength", "6", "--detuning", ".075"]),
    ("detuning001_h02", ["gadget", "--h", ".2", "--detuning", ".01"]),
    ("background_h02", ["triple", "--h", ".2", "--strength", "0"]),
    ("strength_low_h02", ["triple", "--h", ".2", "--strength", "23.76"]),
    ("strength_high_h02", ["triple", "--h", ".2", "--strength", "24.24"]),
    ("absorption001_h02", ["triple", "--h", ".2", "--absorption", ".01"]),
    ("absorption01_h02", ["triple", "--h", ".2", "--absorption", ".1"]),
    ("gadget_o8_h0167", ["gadget", "--h", "0.16666666666666666"]),
    ("modes_o8_h025", ["modes", "--h", ".25"]),
    ("modes_o8_h02", ["modes", "--h", ".2"]),
    ("modes_radius2_h0333", ["modes", "--h", "0.3333333333333333", "--radius", "2",
                            "--separation", "4", "--lengths", "8", "8", "14", "--detuning", ".075"]),
    ("modal_h025", ["modal", "--h", ".25"]),
    ("modal_h02", ["modal", "--h", ".2"]),
    ("modal_radius2_h0333", ["modal", "--h", "0.3333333333333333", "--radius", "2",
                             "--separation", "4", "--lengths", "8", "8", "14", "--detuning", ".075"]),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", nargs="+", choices=[name for name, _ in CASES])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, OPENBLAS_NUM_THREADS="2", OMP_NUM_THREADS="2")
    for name, case_args in CASES:
        if args.cases and name not in args.cases:
            continue
        destination = args.output / name
        if destination.exists():
            raise FileExistsError(f"Refusing to replace prior result: {destination}")
        command = [sys.executable, str(Path(__file__).with_name("maxwell.py")),
                   case_args[0], "--order", "8", "--solver", "cudss", "--strength", "24",
                   *case_args[1:], "--output", str(destination)]
        print(f"START {name}", flush=True)
        start = time.perf_counter()
        with (args.output / f"{name}.log").open("w") as log:
            result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        receipt = {"command": command, "returncode": result.returncode,
                   "elapsed_seconds": time.perf_counter()-start}
        (args.output / f"{name}_process.json").write_text(json.dumps(receipt, indent=2)+"\n")
        print(f"FINISH {name}: {receipt}", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
