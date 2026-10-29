import Maxwell.Continuum.CornerBridgeComplex
import Maxwell.Continuum.CornerBridgeGapReal
import Maxwell.Continuum.RankOneBandBasic

/-! Certified simple-eigenvalue input for the actual continuum cluster. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open ClusterComplement PeriodicPerturbation
open scoped InnerProductSpace

theorem finiteK_gap (u : clusterSpace) (hu : inner ℂ topState u = 0) :
    (1 / 20 : ℝ) * ‖u‖ ^ 2 ≤
      (inner ℂ u ((Corner.lambdaStar : ℂ) • u - finiteK u)).re := by
  have hperp := coordinates_perp u hu
  have hr := real_corner_gap (realPart (coordinates u)) (coordinates_realPart_transverse u) hperp.1
  have hi := real_corner_gap (imagPart (coordinates u)) (coordinates_imagPart_transverse u) hperp.2
  have hform : (inner ℂ u ((Corner.lambdaStar : ℂ) • u - finiteK u)).re =
      Corner.lambdaStar * ‖u‖ ^ 2 - (inner ℂ u (finiteK u)).re := by
    have hs : inner ℂ u ((Corner.lambdaStar : ℂ) • u) =
        (Corner.lambdaStar : ℂ) * inner ℂ u u := inner_smul_right u u _
    rw [inner_sub_right,hs,Complex.sub_re,inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow]
    change (((Corner.lambdaStar : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)).re - _) = _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [hform,coordinates_norm_sq,coordinates_K_form]
  linarith

/-- All spectral data here refer to the actual fixed continuum cluster. -/
theorem actualCornerData : RankOneBand.Data finiteK topState Corner.lambdaStar where
  unit_norm := topState_norm
  symmetric := finiteK_isSymmetric
  eigenvector := finiteK_topState
  gap := finiteK_gap

end Maxwell.Continuum.CornerBridge
