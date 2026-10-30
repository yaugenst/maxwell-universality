import Maxwell.Continuum.SourceRoutingSortReads
import Maxwell.Continuum.NatAssignCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def selected {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) : ℕ→ℕ :=
  selectProgram.evaluate (beforeSelect p round saved i)
def temporary : List ℕ := [1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1221,1222,1223,1224]
def cleanup : List NatAssign.Instruction := NatAssign.clearList temporary++[.add 1219 1201]

theorem selected_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (i : Fin (q*q)) (j : ℕ) (hj : j∉temporary) : selected p round saved i j=seed p round i.val j := by
  have hp : j∉partnerProgram.writes := by
    intro h
    exact hj (List.mem_toFinset.mp ((show partnerProgram.writes⊆temporary.toFinset by decide) h))
  have hs : j∉selectProgram.writes := by
    intro h
    exact hj (List.mem_toFinset.mp ((show selectProgram.writes⊆temporary.toFinset by decide) h))
  have h8 : j≠1208 := by intro h;subst j;exact hj (by decide)
  have h9 : j≠1209 := by intro h;subst j;exact hj (by decide)
  rw [selected,selectProgram.evaluate_other _ _ hs]
  simp only [beforeSelect,afterSelf,Function.update_of_ne h8,Function.update_of_ne h9]
  exact intermediate_other p round i j hp

theorem cleanup_values {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    NatAssign.values cleanup (selected p round saved i)=seed p round (i.val+1) := by
  rw [cleanup,Maxwell.Continuum.RationalDataflow.values_append]
  funext j
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]
  by_cases h1 : j=1201
  · subst j
    rw [Function.update_self,NatAssign.clearList_values,NatAssign.clearList_values]
    simp only [show (1219 : ℕ)∉temporary by decide,show (1201 : ℕ)∉temporary by decide,ite_false,
      selected_other p round saved i 1219 (by decide),selected_other p round saved i 1201 (by decide)]
    change 1+i.val=i.val+1
    omega
  · rw [Function.update_of_ne h1,NatAssign.clearList_values]
    by_cases ht : j∈temporary
    · simp only [ht,ite_true]
      simp only [temporary,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · simp only [ht,ite_false,selected_other p round saved i j ht,seed,h1,ite_false]

private theorem selected_width_arithmetic (B : ℕ) : 2^6*(2^20*(B+1)+1) ≤ 2^27*(B+3) := by omega

theorem selected_width {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(selected p round saved i j).bits.length ≤ 2^27*(p.bound round+3) := by
  have h:=selectProgram.evaluate_width select_valid (beforeSelect p round saved i)
    (2^20*(p.bound round+1)) (beforeSelect_width p round saved fit i) (select_literals _)
  intro j hj
  have actual:=(Nat.le_add_right _ _).trans (h j hj)
  have hstep:=Nat.mul_le_mul_right (2^20*(p.bound round+1)+1)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) select_steps)
  exact actual.trans (hstep.trans (selected_width_arithmetic (p.bound round)))

theorem cleanup_valid : ∀a∈cleanup,a.Valid GeometryArithmetic.ids := by
  simp [cleanup,temporary,NatAssign.clearList,NatAssign.Instruction.Valid,GeometryArithmetic.ids,controls]

theorem cleanup_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (selected p round saved i) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code cleanup) steps s t ∧ steps ≤ 2^130*(p.bound round+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (seed p round (i.val+1)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩:=stage cleanup cleanup_valid (selected p round saved i)
    (2^27*(p.bound round+3)) (selected_width p round saved fit i)
    (by simp [cleanup,temporary,NatAssign.clearList,NatAssign.Instruction.literalWidth]) input tape s bank ready
  refine ⟨steps,t,he,?_,by simpa only [cleanup_values] using bt,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · change steps ≤ 3000*8^15*(2^27*(p.bound round+3)+2)^2 at hc
    calc
      steps ≤ 3000*8^15*(2^27*(p.bound round+3)+2)^2 := hc
      _ ≤ 3000*8^15*(2^28*(p.bound round+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = (3000*8^15*(2^28)^2)*(p.bound round+3)^2 := by ring
      _ ≤ 2^130*(p.bound round+3)^2 := Nat.mul_le_mul_right _ (by decide)
  · intro j hj
    simp only [GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms cleanup_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
