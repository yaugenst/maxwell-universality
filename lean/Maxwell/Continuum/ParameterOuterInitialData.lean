import Maxwell.Continuum.ParameterOuterSearch
import Maxwell.Cost.SelectedParameters.GeometricAdapterBounds
import Maxwell.Cost.SelectedParameters.GeometricCeiling
import Maxwell.Cost.SelectedParameters.RationalChoice
import Maxwell.Cost.Structured.NatAssign.Values

namespace Maxwell.Continuum.Parameters.OuterInitial
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def extra : Finset ℕ := Finset.Icc 2200 2207
def ids : Finset ℕ := GeometricAdapter.ids extra
def setup : List NatAssign.Instruction :=
  [.literal 2202 1,.copy 2200 2203]++List.replicate 5 (.multiply 2200 2203)++
  [.literal 2204 0,.literal 2205 0,.literal 2206 0,.literal 2207 0]++
  GeometricAdapter.clearGeo++Rational.clear
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values setup v
def searched (v : ℕ→ℕ) : ℕ→ℕ :=
  Rational.after (prepared v) 2204 2205 (Nat.clog 8 ((v 2200)^6),1)
def result (v : ℕ→ℕ) : ℕ→ℕ :=
  Rational.after (searched v) 2206 2207 (initialExponent (v 2201) (v 2200),1)
def code : Code := .seq (NatAssign.code setup)
  (.seq (GeometricAdapter.code 1 8 2202 2203 2204 2205)
    (Rational.choiceCode .maximum 2201 2202 2204 2205 2206 2207))
def workspace : Finset ℕ := ids∪{0,1,2,3}
def preparedWidth (B : ℕ) : ℕ := 2^setup.length*(B+2)
def searchWidth (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  Geometric.width (Nat.clog 8 ((v 2200)^6)) 4 (GeometricAdapter.inputWidth 4 (preparedWidth B))
def costBound (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  3000*8^setup.length*(B+3)^2+
    (GeometricAdapter.costBound (Nat.clog 8 ((v 2200)^6)) 4 (preparedWidth B)+
      Rational.choiceCostBound (searchWidth v B))

theorem extra_ge : ∀ i∈extra,540≤ i := by intro i hi;simp only [extra,Finset.mem_Icc] at hi;omega
theorem ids_ge : ∀ i∈ids,4≤ i := GeometricAdapter.ids_ge extra extra_ge
theorem setup_valid : ∀ a∈setup,a.Valid ids := by
  simp [setup,NatAssign.Instruction.Valid,ids,GeometricAdapter.ids,Rational.ids,
    Geometric.extra,extra,GeometricAdapter.clearGeo,Rational.clear,Rational.common]

theorem prepared_fields (v : ℕ→ℕ) :
    prepared v 2200=v 2200 ∧ prepared v 2201=v 2201 ∧ prepared v 2202=1 ∧
      prepared v 2203=(v 2200)^6 := by
  simp [prepared,setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,List.replicate_succ,GeometricAdapter.clearGeo,Rational.clear]
  ring

theorem prepared_zero (v : ℕ→ℕ) (i : ℕ) (hi : i∈Geometric.extra∪Rational.common) :
    prepared v i=0 := by
  simp only [Geometric.extra,Rational.common,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton] at hi
  rcases hi with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [prepared,setup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,List.replicate_succ,
      GeometricAdapter.clearGeo,Rational.clear]
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [prepared,setup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,List.replicate_succ,
      GeometricAdapter.clearGeo,Rational.clear]

theorem searched_fields (v : ℕ→ℕ) :
    searched v 2201=v 2201 ∧ searched v 2202=1 ∧
      searched v 2204=Nat.clog 8 ((v 2200)^6) ∧ searched v 2205=1 := by
  have h := prepared_fields v
  simpa [searched,Rational.after,Rational.common] using And.intro h.2.1 h.2.2.1

theorem chosen (v : ℕ→ℕ) :
    Rational.choicePair .maximum (searched v 2201) (searched v 2202)
      (searched v 2204) (searched v 2205)=(initialExponent (v 2201) (v 2200),1) := by
  obtain ⟨h1,h2,h4,h5⟩ := searched_fields v
  rw [h1,h2,h4,h5]
  simp only [Rational.choicePair,Rational.choose,initialExponent]
  by_cases h : v 2201<Nat.clog 8 ((v 2200)^6)
  · simp [h,max_eq_right h.le]
  · simp [h,max_eq_left (le_of_not_gt h)]

theorem prepared_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀ i∈ids,(v i).bits.length≤B) :
    ∀ i∈ids,(prepared v i).bits.length≤preparedWidth B := by
  have h := NatAssign.values_width ids setup setup_valid v (B+1)
    (fun i hi => (hw i hi).trans (by omega)) (by
      simp [setup,GeometricAdapter.clearGeo,Rational.clear,NatAssign.Instruction.literalWidth])
  intro i hi
  exact (Nat.le_add_right _ 1).trans (by simpa [prepared,preparedWidth,Nat.add_assoc] using h i hi)

#print axioms chosen

end Maxwell.Continuum.Parameters.OuterInitial
