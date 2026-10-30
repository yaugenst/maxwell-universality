import Maxwell.Continuum.WellCutoffDeriv

/-! The actual convolution cutoff as a bounded interval integral. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open MeasureTheory Set Well

def cutoffClamp (x : ℝ) : ℝ := max (-1/2) (min (1/2) x)

theorem cutoffClamp_bounds (x : ℝ) : cutoffClamp x ∈ Icc (-1/2 : ℝ) (1/2) := by
  unfold cutoffClamp
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem cutoffClamp_mono : Monotone cutoffClamp := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_left _ hxy)

theorem cutoffClamp_le_iff {t : ℝ} (ht : |t|<1/2) (x : ℝ) : cutoffClamp x≤t ↔ x≤t := by
  have hlo : (-1/2 : ℝ)≤t := by simpa only [neg_div] using (abs_lt.mp ht).1.le
  have hhi : ¬ (1/2 : ℝ)≤t := (abs_lt.mp ht).2.not_ge
  simp only [cutoffClamp,max_le_iff,min_le_iff,hlo,hhi,true_and,false_or]

theorem le_cutoffClamp_iff {t : ℝ} (ht : |t|<1/2) (x : ℝ) : t≤cutoffClamp x ↔ t≤x := by
  have hlo : ¬ t≤(-1/2 : ℝ) := by simpa only [neg_div] using (abs_lt.mp ht).1.not_ge
  have hhi : t≤(1/2 : ℝ) := (abs_lt.mp ht).2.le
  simp only [cutoffClamp,le_max_iff,le_min_iff,hlo,hhi,false_or,true_and]

theorem psi_eq_clipped_integral (x : ℝ) :
    psi x=(∫ t in cutoffClamp (x-3/2)..cutoffClamp (x+3/2), cutoffBase t)/cutoffNormalization := by
  have hab : cutoffClamp (x-3/2)≤cutoffClamp (x+3/2) := cutoffClamp_mono (by linarith)
  have he (t : ℝ) : cutoffWindow (x-t)*psi0 t=
      (Icc (cutoffClamp (x-3/2)) (cutoffClamp (x+3/2))).indicator psi0 t := by
    by_cases ht : |t|<1/2
    · have hm : x-t ∈ Icc (-3/2 : ℝ) (3/2) ↔
          t ∈ Icc (cutoffClamp (x-3/2)) (cutoffClamp (x+3/2)) := by
        simp only [mem_Icc,cutoffClamp_le_iff ht,le_cutoffClamp_iff ht]
        constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
      by_cases hw : x-t ∈ Icc (-3/2 : ℝ) (3/2)
      · simp [cutoffWindow,hw,hm.mp hw]
      · simp [cutoffWindow,hw,not_congr hm |>.mp hw]
    · have hz := psi0_eq_zero_of_half_le t (le_of_not_gt ht)
      rw [hz,mul_zero]
      by_cases hm : t ∈ Icc (cutoffClamp (x-3/2)) (cutoffClamp (x+3/2)) <;> simp [hm,hz]
  rw [psi_eq_integral]
  simp_rw [he]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  simp only [psi0]
  simp only [div_eq_mul_inv,intervalIntegral.integral_mul_const]

theorem cutoffNormalization_eq_intervalIntegral :
    cutoffNormalization=∫ t in (-1/2 : ℝ)..(1/2 : ℝ), cutoffBase t := by
  rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc]
  change (∫ t, cutoffBase t)=_
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  apply cutoffBase_eq_zero_of_half_le
  by_contra hn
  exact ht (by simpa only [mem_Icc,neg_div] using (abs_le.mp (le_of_lt (lt_of_not_ge hn))))

theorem psi_lipschitz : LipschitzWith 16 psi := by
  apply lipschitzWith_of_nnnorm_deriv_le (psi_contDiff.differentiable (by simp))
  intro x
  have h := psi_iteratedDeriv_succ_bound 0 x
  norm_num only [zero_add,iteratedDeriv_one,pow_zero,Nat.factorial_zero,Nat.cast_one,
    one_pow,mul_one] at h
  exact_mod_cast h

#print axioms psi_eq_clipped_integral
#print axioms psi_lipschitz

end Maxwell.Continuum.Calibration
