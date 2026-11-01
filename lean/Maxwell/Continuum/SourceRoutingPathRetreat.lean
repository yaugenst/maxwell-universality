import Maxwell.Continuum.SourceRoutingHistoryLayout
import Maxwell.Continuum.SourceRoutingGeometryControlValues

/-! Move the geometry reader to the preceding stored comparison layer.
The address subtraction uses charged quotient/remainder arithmetic, so the
program is fixed and the history base need not be aligned to the slab width. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def retreat : Control :=
  Control.prepend [.copy 1200 1225,.multiply 1200 1225,.multiply 1217 1225]
    (.divide 1215 1225 1226 1227 (.decrement 1226
      (Control.prepend [.copy 1215 1216,.copy 1226 1215,.multiply 1225 1215,.add 1227 1215]
        (.decrement 1202 (Control.prepend [.literal 1225 0,.literal 1226 0,.literal 1227 0] .done)))))

theorem retreat_valid : retreat.Valid := by
  simp [retreat,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem stride_positive {q : ℕ} (p : GeometryHistory.Plan q) : 0<p.stride :=
  Nat.mul_pos (Nat.mul_pos p.positive p.positive) (p.layer 0).width_positive

theorem slab_quotient_positive {q : ℕ} (p : GeometryHistory.Plan q) (k : ℕ) :
    0<p.slab (k+1)/p.stride := by
  apply Nat.div_pos
  · dsimp only [GeometryHistory.Plan.slab]
    nlinarith [stride_positive p]
  · exact stride_positive p

theorem slab_predecessor {q : ℕ} (p : GeometryHistory.Plan q) (k : ℕ) :
    p.slab (k+1)%p.stride+p.stride*(p.slab (k+1)/p.stride-1)=p.slab k := by
  have positive := slab_quotient_positive p k
  have decomposition := Nat.mod_add_div (p.slab (k+1)) p.stride
  have previous : p.slab (k+1)/p.stride-1+1=p.slab (k+1)/p.stride := by omega
  have adjacent : p.slab (k+1)=p.slab k+p.stride := by
    dsimp only [GeometryHistory.Plan.slab]
    ring
  nlinarith only [decomposition,previous,adjacent]

theorem retreat_values {q : ℕ} (p : GeometryHistory.Plan q) (k index : ℕ) :
    retreat.evaluate (GeometrySort.seed (p.layer (k+1)) (k+2) index)=
      GeometrySort.seed (p.layer k) (k+1) index := by
  funext j
  by_cases h25 : j=1225
  · subst j; simp [retreat,Control.evaluate,Control.prepend,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h26 : j=1226
  · subst j; simp [retreat,Control.evaluate,Control.prepend,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h27 : j=1227
  · subst j; simp [retreat,Control.evaluate,Control.prepend,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h2 : j=1202
  · subst j; simp [retreat,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h16 : j=1216
  · subst j; simp [retreat,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed,GeometryHistory.Plan.layer]
  by_cases h15 : j=1215
  · subst j
    simpa [retreat,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed,
      GeometryHistory.Plan.layer,GeometryHistory.Plan.stride,GeometrySort.Plan.width,
      GeometryHistory.Plan.width,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using slab_predecessor p k
  simp [retreat,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,h25,h26,h27,h2,h16,h15,GeometrySort.seed,
    GeometryHistory.Plan.layer,GeometrySort.Plan.width]

theorem retreat_executes {q : ℕ} (p : GeometryHistory.Plan q) (k index : ℕ)
    (indexBound : index ≤ q*q) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed (p.layer (k+1)) (k+2) index) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape retreat.code steps s t ∧
      steps ≤ 2^152*((p.layer (k+1)).bound (k+2)+2)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed (p.layer k) (k+1) index) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  have admissible : retreat.Admissible (GeometrySort.seed (p.layer (k+1)) (k+2) index) := by
    simpa [retreat,Control.Admissible,Control.prepend,divided,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed,
      GeometryHistory.Plan.layer,GeometryHistory.Plan.stride,GeometrySort.Plan.width,
      GeometryHistory.Plan.width,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      And.intro (stride_positive p) (slab_quotient_positive p k)
  obtain ⟨steps,t,he,hc,bt,zt,pt,ft⟩ := retreat.executes retreat_valid _
    (GeometrySort.seed_zero _ _ _) admissible ((p.layer (k+1)).bound (k+2))
    (GeometrySort.seed_width _ _ _ indexBound)
    (by simp [retreat,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth])
    input tape s bank ready privateBlank
  refine ⟨steps,t,he,?_,by simpa only [retreat_values] using bt,zt,pt,ft⟩
  exact hc.trans (controlCost_steps _ 14 _ (by decide))

#print axioms retreat_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
