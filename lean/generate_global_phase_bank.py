# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Stage shared phase enclosures; only subsequent Lean kernel checks accept them."""
from pathlib import Path
from fractions import Fraction
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "certificates/yee"
COVER = SOURCE / "work/bulk/global_certificate/cover_proposals.json"
NEGATIVE_COVER = SOURCE / "work/bulk/clean_certificate/cover_screen_complete.json"
INTERVALS = SOURCE / "work/bulk/global_certificate/interval_tools.py"
OUT = ROOT / "Maxwell/Certificate/GlobalPhaseBank"
EVIDENCE = ROOT / "evidence/global_phase_bank"


def main():
    records = json.loads(COVER.read_text())["accepted"]
    negative = json.loads(NEGATIVE_COVER.read_text())["accepted"]
    unique = {Fraction(c) for record in records for c in record["center"]}
    assert len(records) == 2056 and len(unique) == 141
    assert {Fraction(c) for record in negative for c in record["center"]} <= unique
    coordinates = sorted(unique | {Fraction(1, 2)})
    index = {c: i for i, c in enumerate(coordinates)}
    spec = importlib.util.spec_from_file_location("global_phase_proposals", INTERVALS)
    intervals = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(intervals)
    phases = [tuple(int(v) * 16 for v in intervals.cis(c / 20)) for c in coordinates]
    OUT.mkdir(exist_ok=True)
    EVIDENCE.mkdir(exist_ok=True)
    data = ["import Maxwell.Certificate.DyadicKernel", "namespace Maxwell.Certificate.GlobalPhaseBank", "open DyadicKernel"]
    data += ["noncomputable def coordinates : Array (Int × Nat) := #[" + ",".join(f"({c.numerator},{c.denominator})" for c in coordinates) + "]"]
    data += ["noncomputable def phaseData : Array Rectangle := #[" + ",".join("⟨" + ",".join(map(str, p)) + "⟩" for p in phases) + "]"]
    data += ["noncomputable def coordinateIndices : Array (Array Nat) := #[" + ",".join("#[" + ",".join(str(index[Fraction(c)]) for c in rec["center"]) + "]" for rec in records) + "]"]
    data += ["noncomputable def negativeIndices : Array (Array Nat) := #[" + ",".join("#[" + ",".join(str(index[Fraction(c)]) for c in rec["center"]) + "]" for rec in negative) + "]"]
    data += ["end Maxwell.Certificate.GlobalPhaseBank", ""]
    (OUT / "Data.lean").write_text("\n".join(data))
    interface = """import Maxwell.Certificate.GlobalPhaseBank.Data
import Maxwell.Certificate.GlobalGeometry
import Maxwell.Certificate.NegativeGeometry
import Maxwell.Certificate.Trigonometric
import Maxwell.Certificate.DyadicKernelSound
namespace Maxwell.Certificate.GlobalPhaseBank
open DyadicKernel
noncomputable def coordinateQ (i : Fin 142) : ℚ :=
  let q := (coordinates[i.val]?).getD (0,1)
  (q.1:ℚ)/(q.2:ℚ)
noncomputable def phase (i : Fin 142) : Rectangle := (phaseData[i.val]?).getD zero
noncomputable def centerIndex (i : Fin 2056) (j : Fin 3) : Fin 142 :=
  ⟨(((coordinateIndices[i.val]?).getD #[])[j.val]?).getD 0 % 142, Nat.mod_lt _ (by decide)⟩
noncomputable def negativeIndex (i : Fin 604) (j : Fin 3) : Fin 142 :=
  ⟨(((negativeIndices[i.val]?).getD #[])[j.val]?).getD 0 % 142, Nat.mod_lt _ (by decide)⟩
end Maxwell.Certificate.GlobalPhaseBank
"""
    (OUT / "Interface.lean").write_text(interface)
    modules = ["Maxwell.Certificate.GlobalPhaseBank.Data", "Maxwell.Certificate.GlobalPhaseBank.Interface"]
    for i in range(142):
        name = f"Checked{i:03d}"
        (OUT / f"{name}.lean").write_text(f"""import Maxwell.Certificate.GlobalPhaseBank.Interface
namespace Maxwell.Certificate.GlobalPhaseBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase{i:03d}_checked : Trigonometric.cisCheck (coordinateQ {i}/20)
    ((phase {i}).toDyadic.toRectangle 52) = true := by decide +kernel
end Maxwell.Certificate.GlobalPhaseBank
""")
        modules.append(f"Maxwell.Certificate.GlobalPhaseBank.{name}")
    checked = [f"import Maxwell.Certificate.GlobalPhaseBank.Checked{i:03d}" for i in range(142)]
    checked += ["namespace Maxwell.Certificate.GlobalPhaseBank", "theorem phase_checked (i : Fin 142) : Trigonometric.cisCheck (coordinateQ i/20)", "    ((phase i).toDyadic.toRectangle 52) = true := by", "  fin_cases i"]
    checked += [f"  · exact phase{i:03d}_checked" for i in range(142)]
    checked += ["end Maxwell.Certificate.GlobalPhaseBank", ""]
    (OUT / "Checked.lean").write_text("\n".join(checked))
    modules.append("Maxwell.Certificate.GlobalPhaseBank.Checked")
    (EVIDENCE / "modules.json").write_text(json.dumps(modules, indent=2) + "\n")
    manifest = {
        "records": len(records), "phase_count": len(coordinates),
        "coordinate_occurrences": sum(len(r["center"]) for r in records),
        "source_sha256": {str(p.relative_to(SOURCE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in [COVER, NEGATIVE_COVER, INTERVALS]},
        "modules": modules, "status": "proposals; kernel acceptance and geometry binding remain required",
    }
    (EVIDENCE / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"modules": len(modules), "source_bytes": sum(p.stat().st_size for p in OUT.glob("*.lean")), "phase_count": len(coordinates)}))


if __name__ == "__main__":
    main()
