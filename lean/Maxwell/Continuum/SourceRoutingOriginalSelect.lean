import Maxwell.Continuum.SourceRoutingOriginalVertex
import Maxwell.Continuum.SourceRoutingPortIndices

/-! Compute the first incidence port of an original vertex from its stored
enumeration index. All addressing is arithmetic on the geometry controls. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def originalSelectProgram : Control := .divide 1200 1220 1231 1233
  (.divide 1230 1231 1232 1233 (Control.prepend
    [.multiply 1220 1232,.multiply 1200 1232,.multiply 1220 1233,.add 1233 1232,.copy 1232 1201,
      .literal 1230 0,.literal 1231 0,.literal 1232 0,.literal 1233 0] .done))
def originalSelectCode : Code := .seq (loadCode 1257 1230) originalSelectProgram.code

theorem originalSelect_valid : originalSelectProgram.Valid := by
  simp [originalSelectProgram,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem originalSelect_values {half : ℕ} (p : GeometrySort.Plan (2*half)) (round old : ℕ)
    (vertex : Fin (half*half)) :
    originalSelectProgram.evaluate (Function.update (GeometrySort.seed p round old) 1230 vertex.val)=
      GeometrySort.seed p round (finProdFinEquiv (Gluing.tilePort (finProdFinEquiv.symm vertex) 0)).val := by
  have address:=PortIndices.source_exact half vertex 0
  simp only [PortIndices.sourceIndex,Fin.val_zero,Nat.zero_mod,Nat.zero_div,Nat.add_zero] at address
  funext j
  by_cases h1 : j=1201
  · subst j
    change originalSelectProgram.evaluate (Function.update (GeometrySort.seed p round old) 1230 vertex.val) 1201=
      (finProdFinEquiv (Gluing.tilePort (finProdFinEquiv.symm vertex) 0)).val
    rw [address]
    simp [originalSelectProgram,Control.evaluate,Control.prepend,divided,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      GeometrySort.seed]
    ring
  by_cases h30 : j=1230
  · subst j;simp [originalSelectProgram,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h31 : j=1231
  · subst j;simp [originalSelectProgram,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h32 : j=1232
  · subst j;simp [originalSelectProgram,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h33 : j=1233
  · subst j;simp [originalSelectProgram,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  simp [originalSelectProgram,Control.evaluate,Control.prepend,divided,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed,h1,h30,h31,h32,h33]

theorem originalSelect_executes {half : ℕ} (p : GeometrySort.Plan (2*half)) (round old : ℕ)
    (oldBound : old ≤ (2*half)*(2*half)) (vertex : Fin (half*half))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round old) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (vertexWord : Word s.val 1257 vertex.val) :
    ∃steps t,Executes input tape originalSelectCode steps s t ∧
      steps ≤ 2^144*(p.bound round+2)^2 ∧
      NatAssign.Bank ids
        (GeometrySort.seed p round (finProdFinEquiv (Gluing.tilePort (finProdFinEquiv.symm vertex) 0)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  let v:=GeometrySort.seed p round old
  let loaded:=Function.update v 1230 vertex.val
  have vertexBound : vertex.val.bits.length ≤ p.bound round :=
    (Maxwell.Continuum.RationalWords.bits_mono (show vertex.val ≤ (2*half)*(2*half) by
      have h:=vertex.isLt;nlinarith)).trans (p.width_bound round)
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩:=load_executes 1257 1230 (by decide) (by decide)
    v vertex.val input tape s bank ready privateBlank vertexWord
  have width : ∀j∈ids,(loaded j).bits.length ≤ p.bound round := by
    intro j hj
    by_cases same : j=1230
    · subst j;exact vertexBound
    · simpa only [loaded,Function.update_of_ne same] using GeometrySort.seed_width p round old oldBound j hj
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,loaded j=0 := by
    intro j hj
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl <;> rfl
  have halfPositive : 0<half := by have h:=p.positive;omega
  have admissible : originalSelectProgram.Admissible loaded := by
    simp [originalSelectProgram,Control.Admissible,Control.prepend,loaded,v,GeometrySort.seed,
      divided,halfPositive]
  obtain ⟨c₁,t,e₁,h₁,bt,zt,pt,f₁⟩:=originalSelectProgram.executes originalSelect_valid loaded zero
    admissible (p.bound round) width
    (by simp [originalSelectProgram,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth])
    input tape a ba za pa
  refine ⟨c₀+c₁,t,e₀.seq e₁,?_,by simpa only [loaded,v,originalSelect_values] using bt,zt,pt,
    (f₀.mono (by decide)).trans f₁⟩
  have main:=h₁.trans (controlCost_steps _ 11 _ (by decide))
  change c₁ ≤ 2^143*(p.bound round+2)^2 at main
  norm_num [v,GeometrySort.seed] at h₀
  nlinarith only [h₀,main,vertexBound]

#print axioms originalSelect_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
