import Maxwell.Continuum.PeriodicSamplingProduct

/-! Supremum-norm stability of the literal normalized finite DFT. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open scoped Classical

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coefficient_norm_le (N : ℕ) [NeZero N] (f : (ι → ZMod N) → E)
    (k : ι → ZMod N) (C : ℝ) (hf : ∀ j, ‖f j‖ ≤ C) : ‖coefficient N f k‖ ≤ C := by
  rw [coefficient, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((N : ℝ)^Fintype.card ι)⁻¹*∑ j : ι → ZMod N, ‖character N (-k) j • f j‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ((N : ℝ)^Fintype.card ι)⁻¹*∑ _j : ι → ZMod N, C := by
      gcongr with j _
      simpa only [norm_smul, character_norm, one_mul] using hf j
    _ = C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card,
        Finset.prod_const, nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne (N : ℝ))), one_mul]

#print axioms coefficient_norm_le

end Maxwell.Continuum.PeriodicSampling.Product
