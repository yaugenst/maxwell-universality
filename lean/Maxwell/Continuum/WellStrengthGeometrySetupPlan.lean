import Maxwell.Continuum.StoredChronologicalWells
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.Structured.WordCopyAppend
import Maxwell.Cost.Structured.WordCleanup

/-! Literal metadata setup for the strength pass and the eventual placement
serializer. Its operands are the computed geometry, source, and physical words. -/
namespace Maxwell.Continuum.WellStrengthInitialization.Geometry
open Maxwell.Cost Maxwell.Cost.Structured RealizationParameters
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def inputs : Finset ℕ := {141,143,145,153,1209,1250,1252,1253,2221,2227,2244}
def targets : Finset ℕ := GeometryOutput.ids∪{993,994,995,996,998,999}
def ids : Finset ℕ := inputs∪targets
def clearHeaders : List ℕ := targets.sort (·≤·)++[962,972,973]
def work : Finset ℕ := {0,1,2,3}∪targets∪{962,972,973}
def loaded (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈targets then 0 else v i

def populate : List NatAssign.Instruction :=
  [.copy 1252 960,.copy 1250 961,.copy 141 963,.copy 153 964,.copy 1253 965,
   .copy 2221 966,.copy 2227 967,.copy 2244 968,.copy 1209 988,
   .literal 983 (placementNatural 0),.literal 984 (placementNatural 1),.literal 985 (placementNatural 2),
   .copy 145 993,.copy 143 994,.literal 995 2,.literal 996 2]
def instructions : List NatAssign.Instruction := populate++GeometryOutput.preparePlan
def values (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values instructions (loaded v)

theorem inputs_disjoint : Disjoint inputs targets:=by decide

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i:=by
  simp only [ids,inputs,targets,GeometryOutput.ids,Finset.mem_union,Finset.mem_erase,
    Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem valid : ∀a∈instructions,a.Valid ids:=by
  intro a ha
  rcases List.mem_append.mp ha with hp|hp
  · simp only [populate,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals (simp only [NatAssign.Instruction.Valid]; decide)
  · have h:=GeometryOutput.preparePlan_valid a hp
    have subset : GeometryOutput.ids⊆ids:=by
      intro i hi;exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)
    cases a <;> simp only [NatAssign.Instruction.Valid] at h ⊢
    · exact subset h
    all_goals exact ⟨subset h.1,subset h.2.1,h.2.2⟩

theorem literals : ∀a∈instructions,a.literalWidth≤54:=by
  intro a ha
  rcases List.mem_append.mp ha with hp|hp
  · simp only [populate,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  · simp only [GeometryOutput.preparePlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide

theorem changes : NatAssign.changes instructions⊆{0,1,2,3}∪targets:=by decide

theorem values_outside (v : ℕ→ℕ) (i : ℕ) (hi : i∉targets) : values v i=v i:=by
  have targetsValid : ∀a∈instructions,a.target∈targets:=by decide
  rw [values,NatAssign.values_preserves _ _ i (by
    intro a ha he
    exact hi (he ▸ targetsValid a ha))]
  exact ite_eq_right hi

theorem output (v : ℕ→ℕ) :
    values v 960=v 1252 ∧ values v 961=v 1250 ∧ values v 963=v 141 ∧ values v 964=v 153 ∧
    values v 965=v 1253 ∧ values v 966=v 2221 ∧ values v 967=v 2227 ∧ values v 968=v 2244 ∧
    values v 969=3 ∧ values v 970=1 ∧ values v 988=v 1209 ∧
    values v 993=v 145 ∧ values v 994=v 143 ∧ values v 995=2 ∧ values v 996=2 ∧
    values v 998=0 ∧ values v 999=0 := by
  simp [values,instructions,populate,GeometryOutput.preparePlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,loaded,targets,GeometryOutput.ids]

theorem shift (v : ℕ→ℕ) : values v 982=v 2221+v 2221*v 2244+8:=by
  rw [values,instructions,NatAssign.values_append]
  change GeometryOutput.prepared _ 982=_
  rw [GeometryOutput.prepared_shift]
  simp [populate,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,loaded,targets,GeometryOutput.ids]

theorem scale (v : ℕ→ℕ) (j : Fin 3) : values v (983+j.val)=2*v 2221*v 2227*placementNatural j:=by
  rw [values,instructions,NatAssign.values_append]
  change GeometryOutput.prepared _ (983+j.val)=_
  rw [GeometryOutput.prepared_scale]
  fin_cases j <;>
    simp [populate,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,loaded,targets,GeometryOutput.ids]

#print axioms output
#print axioms scale
end Maxwell.Continuum.WellStrengthInitialization.Geometry
