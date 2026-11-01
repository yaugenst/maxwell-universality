import Maxwell.Continuum.SourceRoutingSortLayout
import Maxwell.Continuum.SourceRoutingGeometryControlValues

/-! Actual mixed-radix port transposition at row/column phase boundaries.
The coordinate word is divided by the stored grid width, then rebuilt in
the opposite order; both quotient temporaries are restored to zero. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def transposePort : Control := .divide 1201 1200 1230 1231
  (Control.prepend [.copy 1231 1201,.multiply 1200 1201,.add 1230 1201,
    .literal 1230 0,.literal 1231 0] .done)

theorem transposePort_valid : transposePort.Valid := by
  simp [transposePort,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem transposePort_values {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (start : Port q) :
    transposePort.evaluate (GeometrySort.seed p round (finProdFinEquiv start).val) =
      GeometrySort.seed p round (finProdFinEquiv (start.2,start.1)).val := by
  have quotient : (finProdFinEquiv start).val/q=start.1.val :=
    congrArg (fun a : Port q => a.1.val) (finProdFinEquiv.symm_apply_apply start)
  funext j
  by_cases h1 : j=1201
  · subst j
    change (start.2.val+q*start.1.val)/q=start.1.val at quotient
    simp [transposePort,Control.evaluate,Control.prepend,divided,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      GeometrySort.seed,finProdFinEquiv,quotient,Nat.mod_eq_of_lt start.2.isLt]
  by_cases h30 : j=1230
  · subst j
    simp [transposePort,Control.evaluate,Control.prepend,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h31 : j=1231
  · subst j
    simp [transposePort,Control.evaluate,Control.prepend,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  simp [transposePort,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,h1,h30,h31,GeometrySort.seed]

theorem transposePort_executes {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (start : Port q)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv start).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape transposePort.code steps s t ∧
      steps ≤ 2^128*(p.bound round+2)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv (start.2,start.1)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  have admissible : transposePort.Admissible (GeometrySort.seed p round (finProdFinEquiv start).val) := by
    simp [transposePort,Control.Admissible,Control.prepend,GeometrySort.seed,p.positive]
  obtain ⟨steps,t,he,hc,bt,zt,pt,ft⟩ := transposePort.executes transposePort_valid _
    (GeometrySort.seed_zero p round _) admissible (p.bound round)
    (GeometrySort.seed_width p round _ (finProdFinEquiv start).isLt.le)
    (by simp [transposePort,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth])
    input tape s bank ready privateBlank
  refine ⟨steps,t,he,?_,by simpa only [transposePort_values] using bt,zt,pt,ft⟩
  exact hc.trans (controlCost_steps _ 6 _ (by decide))

#print axioms transposePort_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
