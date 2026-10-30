import Maxwell.Continuum.CalibrationBumpConvolution

namespace Maxwell.Continuum.Calibration

open FreeFiber

theorem exactRootOperator_norm (s : ℝ) (hs : 4 ≤ s) :
    ‖aliasMultiplier (rootTorus s hs)‖ ≤ 1 :=
  (aliasMultiplier_norm _).trans
    ((ContinuousMap.norm_le _ zero_le_one).mpr (rootTorus_norm_le_one s hs))

theorem computedRootOperator_reverse_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    ‖computedRootConvolution s N ell-aliasMultiplier (rootTorus s hs)‖ ≤ (1/2 : ℝ)^N :=
  (norm_sub_rev _ _).trans_le (computedRootConvolution_error s hs N ell hlog)

#print axioms exactRootOperator_norm
#print axioms computedRootOperator_reverse_error

end Maxwell.Continuum.Calibration
