#!/usr/bin/env python3
"""Fresh, isolated computational replay for the Maxwell research checkpoint.

Default mode requires every listed premise, including complete outside-L
coverage. Analytic proofs are separate. A stored PASS string never replaces
execution of the relevant exact/interval verifier.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import time
import traceback
import uuid


ROOT = Path(__file__).resolve().parent
H1 = "work/bulk/clean_certificate"
ISOLATION = "work/bulk/edge_isolation"
GLOBAL_MATRIX = "work/bulk/global_certificate"
GLOBAL_PROPOSAL = GLOBAL_MATRIX + "/cover_proposals.json"
FROZEN_H1_MANIFEST = "f8c0625768ec5c7705408325d49e010195790379b65096b8fb65231543542de0"
FROZEN_GLOBAL_MANIFEST = "bee245fc7edab8fd2de51a4876de665879fc7a9542dfb2a4725fa47a895d100c"
GROUPS = (
    "logical", "composition", "h2-scalars", "original-defect-geometry",
    "pec", "kernel", "bulk-geometry", "h1", "local-inertia",
    "local-defect", "local-scalar", "global",
)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp-" + uuid.uuid4().hex)
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    with temporary.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    if path.read_bytes() != data:
        raise RuntimeError("Atomic output readback failed: " + str(path))


def relative_name(value: str) -> str:
    p = Path(value)
    if p.is_absolute() or not p.parts or any(x in ("..", ".") for x in p.parts):
        raise ValueError("Expected a project-relative path: " + value)
    return p.as_posix()


def source_path(root: Path, value: str) -> Path:
    name = relative_name(value)
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError("Input leaves the research directory: " + name)
    if not p.is_file():
        raise FileNotFoundError("Required input is missing: " + name)
    return p


@dataclass(frozen=True)
class Job:
    name: str
    group: str
    argv: tuple[str, ...]
    inputs: tuple[str, ...]
    outputs: tuple[str, ...] = ()
    special: str = ""
    requires: tuple[str, ...] = ()


def jobs(workers: int, global_proposal: str, global_matrix: str) -> list[Job]:
    sign_checker = "results/bulk/audit_fixed_parameters.py"
    local_sign_proposals = tuple(ISOLATION + "/" + name + "_proposal.json" for name in (
        "lower_1over256", "upper_5over256", "upper_3over128", "upper_7over256", "uniform_local_isolation"))
    result = [
        Job("logical_exact", "logical", ("results/logical/verify_logical.py",),
            ("results/logical/verify_logical.py",)),
        Job("composition_algebra", "composition", ("results/main/verify_composition.py",),
            ("results/main/verify_composition.py",)),
        Job("h2_author_scalars", "h2-scalars", ("results/defects/verify_h2_constants.py",),
            ("results/defects/verify_h2_constants.py",)),
        Job("h2_independent_scalars", "h2-scalars", ("results/logical/verify_h2_scalar_bounds.py",),
            ("results/logical/verify_h2_scalar_bounds.py",)),
        Job("original_defect_geometry", "original-defect-geometry",
            ("results/defects/verify_defect_geometry_independent.py",),
            ("results/defects/verify_defect_geometry_independent.py",)),
        Job("pec_incidence", "pec", ("results/bulk/pec_convention_check.py",),
            ("results/bulk/pec_convention_check.py",)),
        Job("interval_kernel_endpoints", "kernel",
            ("results/bulk/kernel_endpoint_checks.py", "--source", H1),
            ("results/bulk/kernel_endpoint_checks.py", H1 + "/interval_kernel.cpp")),
        Job("independent_h1_geometry", "bulk-geometry",
            ("results/bulk/independent_checks.py", "--source", H1,
             "--output", "artifacts/independent_h1_geometry.json"),
            ("results/bulk/independent_checks.py", H1 + "/cover_screen_complete.json"),
            ("artifacts/independent_h1_geometry.json",)),
        Job("h1_parameter_signs", "h1",
            (sign_checker, "--proposal", H1 + "/cover_screen_complete.json",
             "--output", "artifacts/h1_parameter_signs.json"),
            (sign_checker, H1 + "/cover_screen_complete.json"),
            ("artifacts/h1_parameter_signs.json",)),
        Job("h1_atomic_all_604", "h1",
            (H1 + "/verify_atomic.py", "--workers", str(workers),
             "--output", "artifacts/h1_atomic"), (),
            ("artifacts/h1_atomic/reproduction_summary.json",
             "artifacts/h1_atomic/atomic_point_receipts.json"), "h1", ("h1_parameter_signs",)),
        Job("local_parameter_signs", "local-inertia",
            (sign_checker, *(arg for path in local_sign_proposals for arg in ("--proposal", path)),
             "--output", "artifacts/local_parameter_signs.json"),
            (sign_checker, *local_sign_proposals), ("artifacts/local_parameter_signs.json",)),
        Job("point_inertia_brackets", "local-inertia",
            ("reproduce.py", "--internal-point-inertia", "--internal-output",
             "artifacts/point_inertia_brackets.json"), (),
            ("artifacts/point_inertia_brackets.json",), "point-inertia", ("local_parameter_signs",)),
        Job("uniform_local_isolation", "local-inertia",
            (ISOLATION + "/verify_uniform_local_isolation.py",), (),
            (ISOLATION + "/uniform_local_isolation_acceptance.json",), "uniform", ("local_parameter_signs",)),
        Job("inversion_point_residuals", "local-defect",
            ("results/defects/verify_inversion_point_residuals.py", "--output",
             "artifacts/inversion_point_residuals.json"),
            ("results/defects/verify_inversion_point_residuals.py",
             "results/defects/exact_edge_arithmetic.py",
             "results/defects/inversion_edge_material.json",
             "results/defects/make_inversion_point_witnesses.npz"),
            ("artifacts/inversion_point_residuals.json",)),
    ]
    for label, stem in (("lppm", "explore_inversion_edge_feshbach"),
                        ("lppp", "inversion_feshbach_lppp"),
                        ("lpmp", "inversion_feshbach_lpmp"),
                        ("lmpp", "inversion_feshbach_lmpp")):
        result.append(Job(
            "curvature_gram_" + label, "local-defect",
            ("results/defects/verify_inversion_feshbach_curvature.py", "--stem", stem,
             "--output", "artifacts/curvature_gram_" + label + ".json"),
            ("results/defects/verify_inversion_feshbach_curvature.py",
             "results/defects/exact_edge_arithmetic.py",
             "results/defects/inversion_edge_material.json",
             "results/defects/" + stem + ".npz"),
            ("artifacts/curvature_gram_" + label + ".json",)))
    result.extend([
        Job("whole_neighborhood_scalar_closure", "local-scalar",
            ("results/main/verify_local_edge_scalar.py",),
            ("results/main/verify_local_edge_scalar.py",)),
        Job("global_parameter_signs", "global",
            (sign_checker, "--proposal", global_proposal,
             "--output", "artifacts/global_parameter_signs.json"),
            (sign_checker, global_proposal), ("artifacts/global_parameter_signs.json",)),
        Job("global_atomic_all_boxes", "global",
            (global_matrix + "/verify_global.py", "--workers", str(workers),
             "--output", "artifacts/global_atomic"), (),
            ("artifacts/global_atomic/reproduction_summary.json",
             "artifacts/global_atomic/point_receipts.json",
             "artifacts/global_atomic/geometry_acceptance.json"), "global-atomic", ("global_parameter_signs",)),
        Job("outside_l_independent_binding", "global",
            ("results/defects/verify_outside_l_cover.py", "--proposal", global_proposal,
             "--matrix-dir", global_matrix,
             "--receipts-dir", "artifacts/global_atomic/accepted_points",
             "--require-current-receipts", "--output", "artifacts/outside_l.json"),
            ("results/defects/verify_outside_l_cover.py",),
            ("artifacts/outside_l.json",), "global-geometry", ("global_atomic_all_boxes",)),
    ])
    return result


class Snapshot:
    """Copy exact inputs; never copy old generated acceptance into an output path."""
    def __init__(self, source: Path, destination: Path):
        self.source = source
        self.destination = destination
        self.files: dict[str, dict[str, object]] = {}

    def add(self, name: str, expected: str | None = None, role: str = "input") -> None:
        name = relative_name(name)
        if name in self.files:
            if expected is not None and self.files[name]["sha256"] != expected:
                raise RuntimeError("Conflicting frozen digest: " + name)
            return
        original = source_path(self.source, name)
        digest = sha(original)
        if expected is not None and digest != expected:
            raise RuntimeError("Frozen input digest mismatch: " + name)
        target = self.destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        if sha(target) != digest or sha(original) != digest:
            raise RuntimeError("Input changed during snapshot: " + name)
        self.files[name] = {"sha256": digest, "bytes": target.stat().st_size, "role": role}

    def read(self, name: str) -> object:
        self.add(name)
        return json.loads((self.destination / name).read_text())

    def prepare(self, job: Job, global_proposal: str, global_matrix: str) -> None:
        for name in job.inputs:
            self.add(name)
        if job.special == "h1":
            self.add(H1 + "/evidence_manifest.json", FROZEN_H1_MANIFEST, "frozen_manifest")
            manifest = self.read(H1 + "/evidence_manifest.json")
            if manifest["witness_count"] != 604 or len(manifest["files"]) != 613:
                raise RuntimeError("Unexpected frozen H1 evidence schema")
            for name, digest in manifest["files"].items():
                self.add(H1 + "/" + relative_name(name), digest, "frozen_h1_input")
            atomic = self.read(H1 + "/atomic_driver_manifest.json")
            if atomic["frozen_evidence_manifest_sha256"] != FROZEN_H1_MANIFEST:
                raise RuntimeError("Atomic driver does not bind the frozen H1 manifest")
            self.add(H1 + "/verify_atomic.py", atomic["atomic_driver_sha256"], "source")
        elif job.special in ("point-inertia", "uniform"):
            manifest = self.read(ISOLATION + "/uniform_local_isolation_manifest.json")
            for name in ("verify_point.py", "interval_tools.py", "interval_kernel.cpp", "exact_geometry.py"):
                self.add(ISOLATION + "/" + name, manifest["files"][name], "source")
            if job.special == "point-inertia":
                self.add("reproduce.py", role="source")
                labels = ("lower_1over256", "upper_5over256")
            else:
                self.add(ISOLATION + "/verify_uniform_local_isolation.py",
                         manifest["files"]["verify_uniform_local_isolation.py"], "source")
                labels = ("upper_7over256",)
            for label in labels:
                proposal = label + "_proposal.json"
                self.add(ISOLATION + "/" + proposal, manifest["files"].get(proposal), "proposal")
                record = self.read(ISOLATION + "/" + proposal)
                witness = record["witness"]
                if Path(witness).name != witness:
                    raise ValueError("Unsafe local witness name")
                witness_name = "witnesses/" + witness
                self.add(ISOLATION + "/" + witness_name,
                         manifest["files"].get(witness_name), "witness")
        elif job.special == "global-atomic":
            self.add(global_matrix + "/frozen_manifest.json", FROZEN_GLOBAL_MANIFEST, "frozen_manifest")
            manifest = self.read(global_matrix + "/frozen_manifest.json")
            if manifest["format"] != "outside-L-comparator-frozen-v1":
                raise RuntimeError("Unsupported global frozen manifest schema")
            for name, digest in manifest["source_sha256"].items():
                self.add(global_matrix + "/" + relative_name(name), digest, "source")
            self.add(global_proposal, manifest["proposal_sha256"], "frozen_global_proposal")
            data = self.read(global_proposal)
            seen = set()
            for record in data["accepted"]:
                name = record["witness"]
                if Path(name).name != name or name in seen:
                    raise ValueError("Unsafe or duplicated global witness name")
                seen.add(name)
                entry = manifest["witnesses"][name]
                path = global_matrix + "/witnesses/" + name
                self.add(path, entry["sha256"], "frozen_global_witness")
                if self.files[path]["bytes"] != entry["bytes"]:
                    raise RuntimeError("Global witness byte count differs from manifest")
            if set(manifest["witnesses"]) != seen or manifest["matrix_boxes"] != len(seen):
                raise RuntimeError("Global manifest does not cover exactly the proposed matrices")

    def unchanged(self) -> list[str]:
        return [name for name, info in self.files.items()
                if not (self.destination / name).is_file()
                or sha(self.destination / name) != info["sha256"]]


def point_inertia(output: Path) -> None:
    """Replay the saved point witnesses without an approximate eigensolver."""
    import numpy as np
    base = ROOT / ISOLATION
    subprocess.run([
        "g++", "-O2", "-std=c++17", "-shared", "-fPIC",
        "-fsanitize=undefined", "-fno-sanitize-recover=all",
        str(base / "interval_kernel.cpp"), "-o", str(base / "interval_kernel.so")
    ], check=True)
    sys.path.insert(0, str(base))
    import verify_point as vp
    from interval_tools import I
    original_den = vp.DEN.copy()
    records = []
    for label, increment, count in (("lower_1over256", 1, 2), ("upper_5over256", 5, 4)):
        rec = json.loads((base / (label + "_proposal.json")).read_text())
        assert rec["center"] == [0.5, 0.5, 0.5] and Fraction(rec["halfwidth"]) == 0
        assert rec["negative_count"] == count and Fraction(rec["cell_shift"]) == Fraction(increment, 4)
        name = rec["witness"]
        assert Path(name).name == name
        path = base / "witnesses" / name
        before = sha(path)
        with np.load(path, allow_pickle=False) as w:
            low = w["low"]
            assert low.ndim == 1 and np.issubdtype(low.dtype, np.integer)
            assert len(set(low.tolist())) == len(low) and np.all(low >= 0) and np.all(low < 2000)
            assert w["F"].shape == (2000, 3, count)
            assert w["Fpos"].shape == (2000, 3, 2 * len(low) - count)
            assert w["F"].dtype == np.complex128 and w["Fpos"].dtype == np.complex128
            assert np.isfinite(w["F"]).all() and np.isfinite(w["Fpos"]).all()
            assert max(float(abs(w["F"]).max()), float(abs(w["Fpos"]).max())) < 100
        vp.DEN = np.ascontiguousarray(original_den + increment)
        vp.SIG = I(Fraction(1, 1 << 24))
        checked = vp.verify_record(rec, True)
        assert checked["negative_count"] == count and checked["frequency_halfwidth"] == "1/16777216"
        assert sha(path) == before
        checked.update(witness_sha256=before, electric_shift=str(Fraction(increment, 256)))
        records.append(checked)
    atomic_json(output, {"scope": "Fresh original-diamond point inertia brackets only",
                         "fresh_matrix_checks": 2, "records": records})
    print("FRESH_POINT_INERTIA_BRACKETS_ACCEPTED", flush=True)


def runtime() -> dict[str, object]:
    packages = {}
    for name in ("numpy", "scipy"):
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = None
    compiler = shutil.which("g++")
    version = None
    if compiler:
        result = subprocess.run([compiler, "--version"], capture_output=True, text=True)
        version = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    return {"python": sys.version, "python_executable": sys.executable,
            "platform": platform.platform(), "machine": platform.machine(),
            "packages": packages, "compiler_executable": compiler, "compiler_version": version,
            "assertions_enabled": __debug__, "python_optimization": sys.flags.optimize,
            "threads_per_blas_process": 1,
            "compile_policy": "C++17, signed __int128, UBSan halt on first failure"}


def execute(job: Job, stage: Path, run: Path, timeout: float | None) -> dict[str, object]:
    log = run / "logs" / (job.name + ".log")
    child_argv = list(job.argv)
    path_flags = {"--source", "--output", "--proposal", "--matrix-dir", "--receipts-dir", "--internal-output"}
    for index in range(1, len(child_argv)):
        if child_argv[index - 1] in path_flags:
            child_argv[index] = str(stage / child_argv[index])
    command = [sys.executable, "-u", *child_argv]
    env = dict(os.environ)
    env.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1",
               NUMEXPR_NUM_THREADS="1", PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1",
               UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1")
    env.pop("PYTHONOPTIMIZE", None)
    started = time.monotonic()
    record = {"job": job.name, "group": job.group, "started_utc": utc(),
              "argv_relative_to_snapshot": ["PYTHON", "-u", *job.argv],
              "working_directory": "snapshot", "log": "logs/" + log.name}
    for name in job.outputs:
        if (stage / name).exists():
            raise RuntimeError("Fresh output path already exists: " + name)
    process = None
    timed_out = False
    interrupted = False
    with log.open("xb") as stream:
        try:
            process = subprocess.Popen(command, cwd=stage, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            while process.poll() is None:
                if timeout is not None and time.monotonic() - started > timeout:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGTERM)
                    break
                time.sleep(0.2)
            try:
                code = process.wait(timeout=5 if timed_out else None)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
        except KeyboardInterrupt:
            interrupted = True
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
            code = 130
        stream.flush()
        os.fsync(stream.fileno())
    record.update(exit_code=code, elapsed_seconds=time.monotonic() - started,
                  finished_utc=utc(), timed_out=timed_out, interrupted=interrupted,
                  log_sha256=sha(log), status="PASS" if code == 0 and not timed_out and not interrupted else "FAIL")
    # Preserve the actual subprocess exit before parsing its generated output.
    # A malformed postflight JSON must not erase evidence that it ran.
    atomic_json(run / "jobs" / (job.name + ".process.json"), record)
    if record["status"] == "PASS":
        artifacts = {}
        for name in job.outputs:
            p = stage / name
            if not p.is_file():
                record.update(status="FAIL", validation_error="Missing fresh output: " + name)
                break
            artifacts["snapshot/" + name] = sha(p)
        record["output_sha256"] = artifacts
        if record["status"] == "PASS" and job.special == "h1":
            summary = json.loads((stage / job.outputs[0]).read_text())
            receipts = json.loads((stage / job.outputs[1]).read_text())
            if summary.get("matrix_checks") != 604 or receipts.get("count") != 604 or len(receipts.get("points", {})) != 604:
                record.update(status="FAIL", validation_error="Fresh H1 aggregate is incomplete")
        if record["status"] == "PASS" and job.special == "global-atomic":
            summary = json.loads((stage / job.outputs[0]).read_text())
            receipts = json.loads((stage / job.outputs[1]).read_text())
            geometry = json.loads((stage / job.outputs[2]).read_text())
            expected = len(receipts.get("points", {}))
            if not (expected > 0 and summary.get("matrix_checks") == expected
                    and receipts.get("count") == expected
                    and geometry.get("pending") == 0 and geometry.get("uncovered") == 0
                    and summary.get("all_before_after_witness_hashes_equal") is True
                    and summary.get("all_source_and_proposal_hashes_unchanged") is True
                    and summary.get("all_receipts_atomic_readback_verified") is True):
                record.update(status="FAIL", validation_error="Global fresh atomic aggregate incomplete")
        if record["status"] == "PASS" and job.special == "global-geometry":
            summary = json.loads((stage / job.outputs[0]).read_text())
            if not (summary.get("geometry_complete") is True
                    and summary.get("matrix_receipts_complete") is True
                    and summary.get("pending_input_boxes") == 0
                    and summary.get("matrix_replayed_this_run") is False):
                record.update(status="FAIL", validation_error="Independent complete geometry/receipt binding failed")
    return record


def main() -> int:
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Assertions are mandatory. Do not use -O or PYTHONOPTIMIZE.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("full", "established-checks"), default="full")
    parser.add_argument("--only", nargs="+", choices=GROUPS,
                        help="Explicit partial group selection; requires --mode established-checks")
    parser.add_argument("--workers", type=int, default=4, help="Worker processes in each atomic replay; BLAS threads stay one")
    parser.add_argument("--run-dir", type=Path, help="New directory, which must not already exist")
    parser.add_argument("--step-timeout", type=float, help="Optional seconds per subprocess; timeout is a failure")
    parser.add_argument("--global-proposal", default=GLOBAL_PROPOSAL, help="Project-relative complete-cover proposal")
    parser.add_argument("--global-matrix-dir", default=GLOBAL_MATRIX, help="Project-relative exact verifier/witness directory")
    parser.add_argument("--list-checks", action="store_true", help="Print the check inventory without claiming verification")
    parser.add_argument("--internal-point-inertia", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--internal-output", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.internal_point_inertia:
        if args.internal_output is None:
            parser.error("Internal point check needs an output path")
        point_inertia(args.internal_output)
        return 0
    if args.workers < 1 or (args.step_timeout is not None and args.step_timeout <= 0):
        parser.error("workers and timeout must be positive")
    if args.only and args.mode != "established-checks":
        parser.error("--only requires the explicitly partial --mode established-checks")
    gp = relative_name(args.global_proposal)
    gm = relative_name(args.global_matrix_dir)
    if gp != gm + "/cover_proposals.json":
        parser.error("The frozen global driver requires --global-proposal MATRIX_DIR/cover_proposals.json")
    all_jobs = jobs(args.workers, gp, gm)
    selected_groups = set(args.only or (GROUPS if args.mode == "full" else GROUPS[:-1]))
    selected = [job for job in all_jobs if job.group in selected_groups]
    if args.list_checks:
        print(json.dumps({"verification_performed": False, "mode": args.mode,
                          "checks": [{"name": j.name, "group": j.group, "argv": list(j.argv)} for j in selected]}, indent=2))
        return 0
    run = (args.run_dir or ROOT / "verification" / "runs" /
           (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "_" + uuid.uuid4().hex[:8])).resolve()
    run.mkdir(parents=True, exist_ok=False)
    (run / "logs").mkdir()
    stage = run / "snapshot"
    (stage / "artifacts").mkdir(parents=True)
    snapshot = Snapshot(ROOT, stage)
    snapshot.add("reproduce.py", role="controller_source")
    atomic_json(run / "runtime.json", runtime())
    report = {"schema_version": 1, "mode": args.mode, "started_utc": utc(),
              "full_reproduction_complete": False, "target_theorem_status": "NOT_ASSIGNED_BY_COMPUTATIONAL_RUNNER",
              "analytic_proofs": "Required separately; ordinary proof, not proof-assistant verification",
              "selected_groups": sorted(selected_groups),
              "unselected_groups": [g for g in GROUPS if g not in selected_groups],
              "workers_per_atomic_replay": args.workers,
              "global_replay_and_geometry_are_separate_required_jobs": True,
              "jobs": [], "status": "RUNNING"}
    atomic_json(run / "run_summary.json", report)
    print("RUN_DIRECTORY", run, flush=True)
    aborted = False
    for job in selected:
        print("START", job.name, flush=True)
        try:
            completed = {item["job"]: item["status"] for item in report["jobs"]}
            missing_dependencies = [name for name in job.requires if completed.get(name) != "PASS"]
            if missing_dependencies:
                raise RuntimeError("Required fresh checks did not pass: " + ", ".join(missing_dependencies))
            snapshot.prepare(job, gp, gm)
            atomic_json(run / "input_manifest.json", {"schema_version": 1, "path_base": "snapshot", "files": snapshot.files})
            record = execute(job, stage, run, args.step_timeout)
        except KeyboardInterrupt:
            record = {"job": job.name, "group": job.group, "status": "INTERRUPTED", "error": "KeyboardInterrupt"}
            aborted = True
        except Exception as exc:
            process_record = run / "jobs" / (job.name + ".process.json")
            prior = json.loads(process_record.read_text()) if process_record.is_file() else {}
            suffix = ".postflight_failure.log" if prior else ".preflight_failure.log"
            log = run / "logs" / (job.name + suffix)
            log.write_text(traceback.format_exc())
            record = {"job": job.name, "group": job.group, "status": "FAIL_CLOSED",
                      "error": str(exc), "log": "logs/" + log.name, "log_sha256": sha(log),
                      "exit_code": prior.get("exit_code"), "subprocess_started": bool(prior)}
            if prior:
                record["process_status_file"] = "jobs/" + process_record.name
        report["jobs"].append(record)
        atomic_json(run / "jobs" / (job.name + ".json"), record)
        atomic_json(run / "run_summary.json", report)
        print("END", job.name, record["status"], flush=True)
        if record.get("interrupted") or aborted:
            aborted = True
            break
    changed = snapshot.unchanged()
    atomic_json(run / "input_manifest.json", {"schema_version": 1, "path_base": "snapshot", "files": snapshot.files})
    report["input_integrity"] = {"all_staged_inputs_unchanged": not changed, "changed_paths": changed}
    report["finished_utc"] = utc()
    passed = not aborted and not changed and len(report["jobs"]) == len(selected) and all(r["status"] == "PASS" for r in report["jobs"])
    if passed and args.mode == "full":
        report["status"] = "ALL_COMPUTATIONAL_PREMISES_REPLAYED_ANALYTIC_PROOF_SEPARATE"
        report["full_reproduction_complete"] = True
    elif passed:
        report["status"] = "ESTABLISHED_CHECKS_PASSED_NOT_FULL"
    else:
        report["status"] = "INTERRUPTED_OPEN" if aborted else "FAILED_OR_INCOMPLETE_OPEN"
    atomic_json(run / "run_summary.json", report)
    print(report["status"], flush=True)
    print("SUMMARY", run / "run_summary.json", flush=True)
    return 0 if passed else (130 if aborted else 2)


if __name__ == "__main__":
    raise SystemExit(main())
