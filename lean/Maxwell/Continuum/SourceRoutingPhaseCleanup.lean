import Maxwell.Continuum.SourceRoutingPhaseSemantics
import Maxwell.Continuum.NatAssignCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def temporary : List ℕ := [1202,1203,1204,1205,1206,1207,1208,1209,1210,1211]
def cleanup : List NatAssign.Instruction := NatAssign.clearList temporary++[.add 1219 1201]

theorem output_other (v : ℕ→ℕ) (j : ℕ) (hj : j∉temporary) : output v j=v j := by
  simp only [temporary,List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
  rcases hj with ⟨_,_,h4,h5,h6,h7,h8,h9,h10,h11⟩
  simp [output,finish,thirdDivision,secondDivision,firstDivision,divided,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,Function.update,
    h4,h5,h6,h7,h8,h9,h10,h11]

theorem cleanup_values {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) :
    NatAssign.values cleanup (output (beforeArithmetic p colors i))=seed p (i.val+1) := by
  rw [cleanup,Maxwell.Continuum.RationalDataflow.values_append]
  funext j
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  by_cases h1 : j=1201
  · subst j
    rw [Function.update_self,NatAssign.clearList_values,NatAssign.clearList_values]
    change 1+i.val=i.val+1
    omega
  · rw [Function.update_of_ne h1,NatAssign.clearList_values]
    by_cases ht : j∈temporary
    · simp only [ht,ite_true]
      simp only [temporary,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · simp only [ht,ite_false,output_other _ _ ht]
      have h2 : j≠1202 := by intro h;subst j;exact ht (by decide)
      have h3 : j≠1203 := by intro h;subst j;exact ht (by decide)
      simp only [beforeArithmetic,afterLabels,Function.update_of_ne h2,Function.update_of_ne h3,seed,h1,ite_false]

theorem cleanup_valid : ∀a∈cleanup,a.Valid GeometryArithmetic.ids := by
  simp [cleanup,temporary,NatAssign.clearList,NatAssign.Instruction.Valid,GeometryArithmetic.ids,
    GeometryArithmetic.controls]

theorem cleanup_executes {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (output (beforeArithmetic p colors i)) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : RationalAccumulator.Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code cleanup) steps s t ∧
      steps ≤ 2^60*(p.bound+3)^2 ∧ NatAssign.Bank GeometryArithmetic.ids (seed p (i.val+1)) t.val ∧
      GeometryArray.Ready t.val ∧ RationalAccumulator.Blank t.val 1249 ∧
      BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  obtain ⟨steps,t,he,hcost,bt,zt,ft⟩:=stage cleanup cleanup_valid
    (output (beforeArithmetic p colors i)) (32*(p.bound+1)) (output_width p colors i)
    (by simp [cleanup,temporary,NatAssign.clearList,NatAssign.Instruction.literalWidth])
    input tape s bank ready
  refine ⟨steps,t,he,?_,by simpa only [cleanup_values] using bt,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · change steps ≤ 3000*8^11*(32*(p.bound+1)+2)^2 at hcost
    calc
      steps ≤ 3000*8^11*(32*(p.bound+1)+2)^2 := hcost
      _ ≤ 3000*8^11*(32*(p.bound+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = (3000*8^11*32^2)*(p.bound+3)^2 := by ring
      _ ≤ 2^60*(p.bound+3)^2 := Nat.mul_le_mul_right _ (by decide)
  · intro j hj
    simp only [GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms cleanup_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
