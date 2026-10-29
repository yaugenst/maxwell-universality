import Maxwell.Continuum.CellBandFourierMomentum
import Maxwell.Continuum.CellBandFourierSymmetry
import Maxwell.Continuum.CellBandFourierMean

/-! Reality in physical space includes reversal of the half-integer Fourier
aliases and the fixed phase of the selected corner eigenvector. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization PeriodicBand

theorem reverseAlias_reverseAlias (ν : Alias) : reverseAlias (reverseAlias ν) = ν :=
  reverseAlias.left_inv ν

theorem aliasMomentum_reverse (ν : Alias) :
    aliasMomentum 0 (reverseAlias ν) = -aliasMomentum 0 ν := by
  funext j
  simp only [aliasMomentum, reverseAlias, Equiv.coe_fn_mk, Pi.zero_apply, add_zero,
    Pi.neg_apply, Int.cast_sub, Int.cast_neg, Int.cast_one]
  ring

theorem spatialPhase_star (q : Momentum) (x : Space) :
    star (spatialPhase q x) = spatialPhase (-star q) x := by
  unfold spatialPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal,
    Pi.neg_apply, Pi.star_apply, Complex.star_def, neg_mul, Finset.sum_neg_distrib,
    mul_neg]

theorem phase_star_alias (ν : Alias) (x : Space) :
    star (spatialPhase (aliasMomentum 0 ν) x) =
      spatialPhase (aliasMomentum 0 (reverseAlias ν)) x := by
  rw [spatialPhase_star, aliasMomentum_reverse]
  congr 1
  have h := aliasMomentum_star 0 ν
  simpa only [star_zero] using congrArg Neg.neg h.symm

theorem reversal_star_summable (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    Summable (fun ν => ‖reversal (star u) ν‖) := by
  have h := reverseAlias.summable_iff.mpr hu
  change Summable (fun ν => ‖u (reverseAlias ν)‖) at h
  simpa only [reversal_apply, fiber_star_apply, norm_star] using h

theorem antiperiodicField_star (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    star (antiperiodicField u x) = antiperiodicField (reversal (star u)) x := by
  have h := (antiperiodicField_hasSum u hu x).star
  have hr := reverseAlias.hasSum_iff.mpr h
  change HasSum (fun ν => star (spatialPhase (aliasMomentum 0 (reverseAlias ν)) x •
    u (reverseAlias ν))) (star (antiperiodicField u x)) at hr
  have hh : HasSum (fun ν => spatialPhase (aliasMomentum 0 ν) x • reversal (star u) ν)
      (star (antiperiodicField u x)) := by
    simpa only [star_smul, phase_star_alias, reverseAlias_reverseAlias,
      reversal_apply, fiber_star_apply] using hr
  exact hh.unique (antiperiodicField_hasSum _ (reversal_star_summable u hu) x)

theorem antiperiodicField_smul (c : ℂ) (u : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    antiperiodicField (c • u) x = c • antiperiodicField u x := by
  have hc : Summable (fun ν => ‖(c • u) ν‖) := by
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul] using hu.mul_left ‖c‖
  apply (antiperiodicField_hasSum _ hc x).unique
  simpa only [lp.coeFn_smul, Pi.smul_apply, smul_comm c] using
    (antiperiodicField_hasSum u hu x).const_smul c

theorem antiperiodicField_neg (u : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    antiperiodicField (-u) x = -antiperiodicField u x := by
  simpa only [neg_one_smul] using antiperiodicField_smul (-1) u hu x

/-- The physical gauge matching the selected real sine/cosine corner mode. -/
def cellEigenfunction (t : Momentum) (x : Space) : Polarization :=
  Complex.I • antiperiodicField (normalizedFiberVector t) x

theorem cellEigenfunction_continuous (t : Momentum) : Continuous (cellEigenfunction t) :=
  by
    change Continuous (fun x => Complex.I • antiperiodicField (normalizedFiberVector t) x)
    exact (continuous_const : Continuous (fun _ : Space => Complex.I)).smul
      (antiperiodicField_continuous (normalizedFiberVector t))

theorem cellEigenfunction_antiperiodic (t : Momentum) (x : Space) (j : Fin 3) :
    cellEigenfunction t (x + (2 : ℝ) • coordinateDirection j) = -cellEigenfunction t x := by
  simp only [cellEigenfunction, antiperiodicField_translate, smul_neg]

theorem cellEigenfunction_norm_le {t : Momentum} (ht : t ∈ chart) (x : Space) :
    ‖cellEigenfunction t x‖ ≤ 32 := by
  rw [cellEigenfunction, norm_smul, Complex.norm_I, one_mul]
  exact band_antiperiodicField_norm_le ht x

theorem cellEigenfunction_mean_square (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    (1/8 : ℝ) * ∫ x in physicalCell, ‖cellEigenfunction (realMomentum t) x‖ ^ 2 = 1 := by
  simp only [cellEigenfunction, norm_smul, Complex.norm_I, one_mul]
  exact band_physical_mean_square t ht

theorem cellEigenfunction_real_imaginary {t : Momentum} (ht : t ∈ chart)
    (hi : star t = -t) (x : Space) :
    star (cellEigenfunction t x) = cellEigenfunction t x := by
  rw [cellEigenfunction, star_smul,
    antiperiodicField_star _ (normalizedFiberVector_fourier_l1 ht).1,
    normalizedFiberVector_imaginary ht hi,
    antiperiodicField_neg _ (normalizedFiberVector_fourier_l1 ht).1]
  simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]

#print axioms antiperiodicField_star
#print axioms cellEigenfunction_mean_square
#print axioms cellEigenfunction_real_imaginary

end Maxwell.Continuum.CellBandFourier
