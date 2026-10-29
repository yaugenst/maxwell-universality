import Maxwell.Spectral.GammaInertia
import Maxwell.Spectral.MagneticThreshold

/-! The larger Gamma cube used by the clean 604-box certificate needs only
the negative trial family, not the high positive Schur calculation. -/

noncomputable section
namespace Maxwell.Spectral.GammaNegative
open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum Direction)
open BoxSymbols BoxFourierProjection GammaInertia

theorem displacement (c : Momentum) (hc : ∀ j, |c j| ≤ 3/16) :
    phaseScale * momentumNorm c ≤ 11/100 := by
  have hn : momentumNorm c^2 ≤ 27/256 := by
    rw [momentumNorm_sq, Fin.sum_univ_three]
    have h (j : Direction) : (c j)^2 ≤ (3/16 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
    linarith [h 0, h 1, h 2]
  have hp : phaseScale ≤ 22/70 := by
    unfold phaseScale
    linarith [Real.pi_lt_d4]
  have hn0 : 0 ≤ momentumNorm c := norm_nonneg _
  have hn1 : momentumNorm c ≤ 1/3 := by nlinarith
  have hm := mul_le_mul hp hn1 hn0 (by norm_num : (0 : ℝ) ≤ 22/70)
  norm_num at hm ⊢
  linarith

theorem low (c : Momentum) (hc : ∀ j, |c j| ≤ 3/16) :
    laplacianSymbol c 0 < 1/64 - 1/4096 := by
  have hz : longitudinalVector 0 0 = 0 := by
    ext j
    fin_cases j <;> simp [longitudinalVector, symbol, shiftSymbol, reciprocalIndex]
  have h := (longitudinal_increment_bound 0 c 0).trans (displacement c hc)
  simp only [zero_add, hz, sub_zero] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [longitudinalVector_norm_sq] at hs
  linarith

theorem high_nonzero (c : Momentum) (hc : ∀ j, |c j| ≤ 3/16)
    (f : Frequency) (hf : f ≠ 0) : laplacianSymbol c f ≠ 0 := by
  have h := BoxGeometry.longitudinal_norm_shift_lower_uniform 0 c f
    (11/100) (53/100) (displacement c hc) (GammaSymbols.nonzero_center_norm f hf)
  simp only [zero_add] at h
  rw [← longitudinalVector_norm_sq]
  exact ne_of_gt (sq_pos_of_pos (by linarith))

theorem magnetic_negative_count (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum)
    (hc : ∀ j, |c j| ≤ 3/16) :
    2002 ≤ (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c (1/64-1/4096)).eigenvalues rfl i < 0).card := by
  have hd := (highSpace c).finrank_add_finrank_orthogonal
  rw [highSpace_finrank_of_nonzero c (high_nonzero c hc)] at hd
  have hdim : Module.finrank ℂ FourierSpace = 6000 := by simp [FourierSpace, Electric, Cell]
  rw [hdim] at hd
  have hn : Module.finrank ℂ (highSpace c)ᗮ = 2002 := by omega
  have h := finrank_le_card_negative_of_trial
    (shiftedMagneticFourier material c (1/64-1/4096)).toEuclideanLin
    (shiftedMagneticFourier_symmetric material c (1/64-1/4096)) (highSpace c)ᗮ.subtype
    (orthogonal_negative_of_low material hm c _ (low c hc))
  simpa only [hn] using h

/-- The clean Gamma cube certifies at least 2002 negative directions of
the true electric operator at the reduced frequency `t-1/4096`. -/
theorem electric_negative_count (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum)
    (hc : ∀ j, |c j| ≤ 3/16) :
    2002 ≤ (Finset.univ.filter fun i =>
      (MagneticThreshold.electric_symmetric material (boundaryMomentum c)
        (1/64-1/4096)).eigenvalues rfl i < 0).card := by
  rw [MagneticThreshold.electric_threshold_negative_count material c _ (by norm_num)
    (fun e => by linarith [hm e])]
  exact magnetic_negative_count material hm c hc

end Maxwell.Spectral.GammaNegative
