import Maxwell.Continuum.SourceRoutingGeometryControlWrites

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def selectBranch : Control := .positive 1211
  (.positive 1223 (.assign (.copy 1209 1212) .done) (.assign (.copy 1208 1212) .done))
  (.positive 1223 (.assign (.copy 1208 1212) .done) (.assign (.copy 1209 1212) .done))
def selectProgram : Control := Control.prepend [.copy 1208 1222,.add 1219 1222]
  (.divide 1209 1222 1223 1224 selectBranch)
def selectPrepared (v : ℕ→ℕ) : ℕ→ℕ := divided
  (NatAssign.values [.copy 1208 1222,.add 1219 1222] v) 1209 1222 1223 1224

theorem select_valid : selectProgram.Valid := by
  simp [selectProgram,selectBranch,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]
theorem select_steps : selectProgram.steps ≤ 6 := by decide
theorem select_literals (B : ℕ) : selectProgram.Literals B := by
  simp [selectProgram,selectBranch,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth]
theorem select_admissible (v : ℕ→ℕ) (one : v 1219=1) : selectProgram.Admissible v := by
  simp [selectProgram,selectBranch,Control.Admissible,Control.prepend,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,one]

theorem select_evaluate (v : ℕ→ℕ) : selectProgram.evaluate v=selectBranch.evaluate (selectPrepared v) := rfl

theorem select_result (v : ℕ→ℕ) (one : v 1219=1) :
    selectProgram.evaluate v 1212=if 0<v 1211 then max (v 1208) (v 1209) else min (v 1208) (v 1209) := by
  let d:=selectPrepared v
  have quotient : 0<d 1223 ↔ v 1208<v 1209 := by
    change 0<v 1209/(v 1219+v 1208) ↔ v 1208<v 1209
    rw [one]
    constructor
    · intro h
      by_contra hh
      have hz:=Nat.div_eq_of_lt (show v 1209<1+v 1208 by omega)
      omega
    · intro h;exact Nat.div_pos (by omega) (by omega)
  have flag : d 1211=v 1211 := rfl
  rw [select_evaluate]
  change selectBranch.evaluate d 1212=_
  by_cases chooseMax : 0<v 1211
  · rw [show selectBranch.evaluate d=
      (Control.positive 1223 (.assign (.copy 1209 1212) .done) (.assign (.copy 1208 1212) .done)).evaluate d
      from Control.positive_true _ _ _ _ (by simpa only [flag] using chooseMax)]
    by_cases less : v 1208<v 1209
    · rw [Control.positive_true _ _ _ _ (quotient.mpr less)]
      simpa only [chooseMax,ite_true,max_eq_right less.le] using (show
        (Control.assign (.copy 1209 1212) .done).evaluate d 1212=v 1209 from rfl)
    · rw [Control.positive_false _ _ _ _ (fun h => less (quotient.mp h))]
      simpa only [chooseMax,ite_true,max_eq_left (Nat.le_of_not_gt less)] using (show
        (Control.assign (.copy 1208 1212) .done).evaluate d 1212=v 1208 from rfl)
  · rw [show selectBranch.evaluate d=
      (Control.positive 1223 (.assign (.copy 1208 1212) .done) (.assign (.copy 1209 1212) .done)).evaluate d
      from Control.positive_false _ _ _ _ (by simpa only [flag] using chooseMax)]
    by_cases less : v 1208<v 1209
    · rw [Control.positive_true _ _ _ _ (quotient.mpr less)]
      simpa only [chooseMax,ite_false,min_eq_left less.le] using (show
        (Control.assign (.copy 1208 1212) .done).evaluate d 1212=v 1208 from rfl)
    · rw [Control.positive_false _ _ _ _ (fun h => less (quotient.mp h))]
      simpa only [chooseMax,ite_false,min_eq_right (Nat.le_of_not_gt less)] using (show
        (Control.assign (.copy 1209 1212) .done).evaluate d 1212=v 1209 from rfl)

#print axioms select_result
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
