import Maxwell.Continuum.DetuningGrid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Finite independent fair bits, their explicit binary value, and the exact
uniform midpoint-grid law. -/

noncomputable section
namespace Maxwell.Continuum.FairBits
open scoped ENNReal

def law (r : ℕ) : PMF (Fin r → Bool) := PMF.uniformOfFintype _

theorem joint_probability (r : ℕ) (w : Fin r → Bool) :
    law r w=∏ _ : Fin r,(1/2 : ℝ≥0∞) := by
  simp [law,PMF.uniformOfFintype_apply,Fintype.card_bool,one_div,ENNReal.inv_pow]

def binaryEquiv (r : ℕ) : (Fin r → Bool) ≃ Fin (2^r) :=
  (Equiv.piCongrRight (fun _ => finTwoEquiv.symm)).trans finFunctionFinEquiv

theorem binaryEquiv_value (r : ℕ) (w : Fin r → Bool) :
    (binaryEquiv r w).val=∑i : Fin r,(finTwoEquiv.symm (w i)).val*2^i.val := rfl

theorem uniform_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α≃β) : (PMF.uniformOfFintype α).map e=PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply,tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply,Fintype.card_congr e]
  · intro a ha
    have hb : b≠e a := by
      intro h
      apply ha
      exact e.injective (h.symm.trans (e.apply_symm_apply b).symm)
    simp only [ite_eq_right hb]

theorem uniform_fin_values (J : ℕ) (hJ : 0<J) :
    letI : NeZero J := ⟨Nat.ne_of_gt hJ⟩
    (PMF.uniformOfFintype (Fin J)).map Fin.val=DetuningGrid.gridLaw J hJ := by
  let : NeZero J := ⟨Nat.ne_of_gt hJ⟩
  classical
  ext k
  rw [PMF.map_apply]
  by_cases hk : k<J
  · rw [tsum_eq_single (⟨k,hk⟩ : Fin J)]
    · simp [PMF.uniformOfFintype_apply,DetuningGrid.gridLaw,PMF.uniformOfFinset_apply,hk]
    · intro a ha
      have he : k≠a.val := by
        intro h
        apply ha
        exact Fin.ext h.symm
      simp only [ite_eq_right he]
  · have hzero : ∀a : Fin J, ¬k=a.val := fun a h => hk (h ▸ a.isLt)
    simp [hzero,DetuningGrid.gridLaw,PMF.uniformOfFinset_apply,hk]

theorem binary_law (r : ℕ) :
    (law r).map (fun w => (binaryEquiv r w).val)=
      DetuningGrid.gridLaw (2^r) (by positivity) := by
  have he := uniform_equiv (binaryEquiv r)
  have hv := uniform_fin_values (2^r) (by positivity)
  rw [← he,PMF.map_comp] at hv
  exact hv

#print axioms joint_probability
#print axioms binaryEquiv_value
#print axioms binary_law

end Maxwell.Continuum.FairBits
