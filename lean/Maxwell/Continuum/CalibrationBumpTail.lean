import Maxwell.Continuum.CalibrationBumpTorus
import Maxwell.Continuum.PeriodicSamplingReconstruction

/-! Full Fourier summability and quantitative truncation of the literal
periodic compact root. No Fourier tail is discarded as an assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open Bloch Well UnitAddTorus PeriodicSampling

attribute [local irreducible] rootTorus

theorem stretched_radius_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : Bloch.Alias => Real.exp (-a*Real.sqrt (imageRadius n))) := by
  apply Summable.of_norm_bounded_eventually (latticeWeight_summable.mul_left (latticeDecayConstant a))
  filter_upwards [Filter.eventually_cofinite_ne (0 : Bloch.Alias)] with n hn
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact stretched_lattice_majorant ha n hn

theorem rootTorus_coefficients_summable (s : ℝ) (hs : 4 ≤ s) :
    Summable (fun n : Bloch.Alias => ‖mFourierCoeff (rootTorus s hs) n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (rootTorus_coefficient_decay s hs)
    ((stretched_radius_summable (rootDecayRate_pos (by linarith : 0 < s))).mul_left (24/s^3))

theorem outside_cube_radius (R : ℕ) (n : Bloch.Alias) (hn : ∃ i, (R : ℤ) ≤ |n i|) :
    (R : ℝ) ≤ (imageRadius n : ℝ) := by
  obtain ⟨i, hi⟩ := hn
  have hc : (R : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast hi
  exact hc.trans (coordinate_le_imageRadius n i)

theorem rootTorus_cubeTail (s : ℝ) (hs : 4 ≤ s) (R : ℕ) (hR : 0 < R) :
    Product.cubeTail (ι := Fin 3) (E := ℂ) (mFourierCoeff (rootTorus s hs)) (R : ℤ) ≤
      (24/s^3)*(64*latticeDecayConstant (rootDecayRate s/2)*
        Real.exp (-(rootDecayRate s/2)*Real.sqrt R)) := by
  have hs0 : 0 < s := by linarith
  have ha := rootDecayRate_pos hs0
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hm (n : Bloch.Alias) :
      (if ∃ i, (R : ℤ) ≤ |n i| then ‖mFourierCoeff (rootTorus s hs) n‖ else 0) ≤
        (24/s^3)*latticeTail (rootDecayRate s) R n := by
    by_cases hn : ∃ i, (R : ℤ) ≤ |n i|
    · rw [ite_eq_left hn, latticeTail, ite_eq_left (outside_cube_radius R n hn)]
      exact rootTorus_coefficient_decay s hs n
    · rw [ite_eq_right hn]
      exact mul_nonneg (by positivity) (latticeTail_nonneg _ _ _)
  have hc : Summable (fun n : Bloch.Alias =>
      if ∃ i, (R : ℤ) ≤ |n i| then ‖mFourierCoeff (rootTorus s hs) n‖ else 0) := by
    convert! Product.cubeTail_summable (mFourierCoeff (rootTorus s hs))
      (rootTorus_coefficients_summable s hs) (R : ℤ) using 1
    funext n
    by_cases hn : ∃ i, (R : ℤ) ≤ |n i| <;> simp only [hn, ↓reduceIte]
  have ht : Summable (fun n : Bloch.Alias => (24/s^3)*latticeTail (rootDecayRate s) R n) :=
    (latticeTail_summable ha hRr).mul_left (24/s^3)
  have hsum := hc.tsum_le_tsum hm ht
  rw [tsum_mul_left] at hsum
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left (latticeTail_sum_bound ha hRr)
    (by positivity : 0 ≤ 24/s^3))
  unfold Product.cubeTail
  convert! hfinal using 1
  apply tsum_congr
  intro n
  by_cases hn : ∃ i, (R : ℤ) ≤ |n i| <;> simp only [hn, ↓reduceIte]

theorem rootTorus_reconstruction (s : ℝ) (hs : 4 ≤ s) (x : UnitAddTorus (Fin 3)) :
    (∑' n : Bloch.Alias, mFourier n x*mFourierCoeff (rootTorus s hs) n) = rootTorus s hs x :=
  Product.reconstruction _ (rootTorus_coefficients_summable s hs) x

#print axioms rootTorus_cubeTail
#print axioms rootTorus_reconstruction

end Maxwell.Continuum.Calibration
