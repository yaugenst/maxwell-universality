# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Split exact phase-index bindings into bounded kernel declarations."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "Maxwell/Certificate/GlobalPhaseBank"
EVIDENCE = ROOT / "evidence/global_phase_bank"


def main():
    core = """import Maxwell.Certificate.GlobalPhaseBank.Interface
namespace Maxwell.Certificate.GlobalPhaseBank
def recordIndex (N offset size : ℕ) (hs : offset+size ≤ N) (k : Fin size) : Fin N :=
  ⟨offset+k.val,by omega⟩
theorem of_block (N offset size : ℕ) (hs : offset+size ≤ N) (P : Fin N → Prop)
    (h : ∀ k, P (recordIndex N offset size hs k)) (i : Fin N)
    (hlo : offset ≤ i.val) (hhi : i.val < offset+size) : P i := by
  let k : Fin size := ⟨i.val-offset,by omega⟩
  have he : recordIndex N offset size hs k = i := by
    apply Fin.ext
    simp only [recordIndex,k]
    omega
  simpa only [he] using h k
end Maxwell.Certificate.GlobalPhaseBank
"""
    (OUT / "GeometryCore.lean").write_text(core)
    modules = ["Maxwell.Certificate.GlobalPhaseBank.GeometryCore"]
    imports = []
    proofs = []
    for tag, count, index, source in [
        ("Center", 2056, "centerIndex", "FrozenGlobal"),
        ("Negative", 604, "negativeIndex", "FrozenNegative"),
    ]:
        blocks = []
        predicate = f"fun i => ∀ j : Fin 3, coordinateQ ({index} i j) = {source}.centerQ i j"
        for block, offset in enumerate(range(0, count, 32)):
            size = min(32, count-offset)
            name = f"Geometry{tag}{block:03d}"
            theorem = f"{tag.lower()}_block{block:03d}"
            text = f"""import Maxwell.Certificate.GlobalPhaseBank.GeometryCore
namespace Maxwell.Certificate.GlobalPhaseBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem {theorem} : ∀ k : Fin {size},
    ({predicate}) (recordIndex {count} {offset} {size} (by decide) k) := by decide +kernel
end Maxwell.Certificate.GlobalPhaseBank
"""
            (OUT / f"{name}.lean").write_text(text)
            module = f"Maxwell.Certificate.GlobalPhaseBank.{name}"
            modules.append(module)
            imports.append(f"import {module}")
            blocks.append(f"  · exact of_block {count} {offset} {size} (by decide) ({predicate}) {theorem} i (by omega) (by omega) j")
        public = "center_binding" if tag == "Center" else "negative_binding"
        proofs += [f"theorem {public} (i : Fin {count}) (j : Fin 3) :",
                   f"    coordinateQ ({index} i j) = {source}.centerQ i j := by",
                   f"  have hi : i.val/32 < {len(blocks)} := by omega",
                   "  interval_cases hq : i.val/32"] + blocks
    (OUT / "Geometry.lean").write_text("\n".join(imports + ["namespace Maxwell.Certificate.GlobalPhaseBank"] + proofs + ["end Maxwell.Certificate.GlobalPhaseBank", ""]))
    modules.append("Maxwell.Certificate.GlobalPhaseBank.Geometry")
    modules += json.loads((ROOT / "evidence/global_schur_proposals/Record0000Signed_modules.json").read_text())
    (EVIDENCE / "geometry_modules.json").write_text(json.dumps(modules, indent=2) + "\n")


if __name__ == "__main__":
    main()
