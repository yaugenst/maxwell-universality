import Maxwell.Continuum.AuxiliaryMomentumProjection

/-! The reciprocal-cell distance controls physical Fourier-frequency
differences across every pair of aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Bloch

theorem quasi_coordinate_minimal (q : QuasiCell) (j : Fin 3) (n : ℤ) :
    |q.val j| ≤ |q.val j + Real.pi * (n : ℝ)| := by
  have hx := q.property j
  have habs : |q.val j| ≤ Real.pi/2 := abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hni : n ≤ -1 := by omega
    have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hni
    have hm := mul_le_mul_of_nonneg_left hnr Real.pi_pos.le
    exact le_trans (by linarith) (neg_le_abs (q.val j + Real.pi * (n : ℝ)))
  · simp [hn]
  · have hni : 1 ≤ n := by omega
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hni
    have hm := mul_le_mul_of_nonneg_left hnr Real.pi_pos.le
    exact le_trans (by linarith) (le_abs_self (q.val j + Real.pi * (n : ℝ)))

theorem quasi_norm_minimal (q : QuasiCell) (n : Alias) :
    ‖q.val‖ ≤ ‖q.val + Real.pi • integerVector n‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change ‖q.val j‖^2 ≤ ‖q.val j + Real.pi*(n j : ℝ)‖^2
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (quasi_coordinate_minimal q j (n j))

theorem quasi_norm_le_shifted_difference (q r : QuasiCell) (n : Alias) :
    ‖q.val‖ ≤ ‖q.val-r.val+Real.pi • integerVector n‖ + ‖r.val‖ := by
  calc
    _ ≤ ‖q.val+Real.pi • integerVector n‖ := quasi_norm_minimal q n
    _ = ‖(q.val-r.val+Real.pi • integerVector n)+r.val‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem quasiFrequencyJoin_difference (q r : QuasiCell) (n m : Alias) :
    (2*Real.pi : ℝ) • (quasiFrequencyJoin (q,n)-quasiFrequencyJoin (r,m)) =
      q.val-r.val+Real.pi • integerVector (n-m) := by
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, quasiFrequencyJoin_apply,
    integerVector_apply, Pi.sub_apply, Int.cast_sub, smul_eq_mul]
  field_simp
  ring

theorem quasiFrequencyJoin_separation {s Δ : ℝ} (q r : QuasiCell) (n m : Alias)
    (hq : s ≤ ‖q.val‖) (hr : ‖r.val‖ ≤ s-Δ) :
    Δ ≤ (2*Real.pi) * ‖quasiFrequencyJoin (q,n)-quasiFrequencyJoin (r,m)‖ := by
  have hm := quasi_norm_le_shifted_difference q r (n-m)
  rw [← quasiFrequencyJoin_difference, norm_smul, Real.norm_of_nonneg (by positivity)] at hm
  linarith

def quasiRadius (ξ : Space) : ℝ := ‖(quasiFrequencyJoin.symm ξ).1.val‖

theorem quasiRadius_measurable : Measurable quasiRadius :=
  (measurable_subtype_coe.comp (measurable_fst.comp quasiFrequencyJoin.symm.measurable)).norm

theorem quasiRadius_join (q : QuasiCell) (n : Alias) :
    quasiRadius (quasiFrequencyJoin (q,n)) = ‖q.val‖ := by
  rw [quasiRadius, quasiFrequencyJoin.symm_apply_apply]

theorem physicalFrequency_separation {s Δ : ℝ} {ξ η : Space}
    (hξ : s ≤ quasiRadius ξ) (hη : quasiRadius η ≤ s-Δ) :
    Δ ≤ (2*Real.pi) * ‖ξ-η‖ := by
  have h := quasiFrequencyJoin_separation (quasiFrequencyJoin.symm ξ).1
    (quasiFrequencyJoin.symm η).1 (quasiFrequencyJoin.symm ξ).2
    (quasiFrequencyJoin.symm η).2 hξ hη
  simpa only [Prod.eta, quasiFrequencyJoin.apply_symm_apply] using h

#print axioms physicalFrequency_separation

end Maxwell.Continuum.Bloch
