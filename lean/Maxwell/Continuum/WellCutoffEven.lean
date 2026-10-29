import Maxwell.Continuum.WellCutoff

/-! Evenness of the literal convolution cutoff and its product. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set

theorem cutoffBase_neg (s : ℝ) : cutoffBase (-s) = cutoffBase s := by
  simp only [cutoffBase, neg_sq]

theorem psi0_neg (s : ℝ) : psi0 (-s) = psi0 s := by
  rw [psi0, psi0, cutoffBase_neg]

theorem cutoffWindow_neg (s : ℝ) : cutoffWindow (-s) = cutoffWindow s := by
  have hm : -s ∈ Icc (-3 / 2 : ℝ) (3 / 2) ↔ s ∈ Icc (-3 / 2 : ℝ) (3 / 2) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [cutoffWindow, Set.indicator_apply, hm]

theorem psi_neg (s : ℝ) : psi (-s) = psi s := by
  rw [psi_eq_integral, psi_eq_integral]
  calc
    _ = ∫ t : ℝ, cutoffWindow (-s - -t) * psi0 (-t) :=
      (integral_neg_eq_self (fun t : ℝ => cutoffWindow (-s - t) * psi0 t) volume).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [show -s - -t = -(s - t) by ring, cutoffWindow_neg, psi0_neg]

theorem chi_neg (q₀ : ℝ) (q : Space) : chi q₀ (-q) = chi q₀ q := by
  unfold chi
  apply Finset.prod_congr rfl
  intro j _
  change psi (-q j / q₀) = psi (q j / q₀)
  rw [neg_div, psi_neg]

end Maxwell.Continuum.Well
