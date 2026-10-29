import Maxwell.Composition.OperatingBackground
import Maxwell.Defect.PhysicalBirmanSchwinger

/-! Coordinate reality of the actual infinite operator and every translated
weighted resolvent block. This identifies the complex axial lower bound with
the real scalar used by calibration. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Green.PhysicalCompression
open scoped InnerProduct

theorem fieldPullback_star (p : Equiv.Perm Edge) (x : Field) :
    fieldPullback p (star x) = star (fieldPullback p x) := by
  ext e
  rfl

theorem yeeCurl_star (x : Field) : yeeCurl (star x) = star (yeeCurl x) := by
  simp only [yeeCurl, add_apply, sub_apply, star_add, star_sub, fieldPullback_star]

theorem yeeCurl_adjoint_star (x : Field) :
    yeeCurl.adjoint (star x) = star (yeeCurl.adjoint x) := by
  simp only [yeeCurl, map_add, map_sub, FiniteStencil.fieldPullback_adjoint,
    add_apply, sub_apply, star_add, star_sub, fieldPullback_star]

theorem electricOperator_star (m : Edge → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K) (x : Field) :
    electricOperator m K hK hm (star x) = star (electricOperator m K hK hm x) := by
  ext e
  simp only [electricOperator, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    yeeCurl_star, yeeCurl_adjoint_star, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, realSequenceMultiplier_apply, lp.star_apply, star_sub, star_mul,
    smul_eq_mul]
  simp
  ring

theorem inverse_star (A : Field →L[ℂ] Field) (hA : IsUnit A)
    (hreal : ∀ x, A (star x) = star (A x)) (x : Field) :
    Ring.inverse A (star x) = star (Ring.inverse A x) := by
  have hleft (y : Field) : Ring.inverse A (A y) = y :=
    congrArg (fun T : Field →L[ℂ] Field => T y) (Ring.inverse_mul_cancel A hA)
  have hright (y : Field) : A (Ring.inverse A y) = y :=
    congrArg (fun T : Field →L[ℂ] Field => T y) (Ring.mul_inverse_cancel A hA)
  rw [← hleft (star (Ring.inverse A x)), hreal, hright]

theorem defectInjection_real {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℝ (Fin N)) :
    star (defectInjection edges W (realCoordinateEmbedding u)) =
      defectInjection edges W (realCoordinateEmbedding u) := by
  ext e
  by_cases he : e ∈ Set.range edges
  · obtain ⟨i, rfl⟩ := he
    simp [lp.star_apply, defectInjection_apply_at]
  · simp [lp.star_apply, defectInjection_apply_of_notMem edges W _ e he]

theorem weightedBlock_real {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (hreal : ∀ x, T (star x) = star (T x))
    (n : Site) (u : EuclideanSpace ℝ (Fin N)) :
    realCoordinateEmbedding (realPartOperator (weightedBlock edges W T n) u) =
      weightedBlock edges W T n (realCoordinateEmbedding u) := by
  have hr : star (T (defectInjection (translatedEmbedding edges n) W (realCoordinateEmbedding u))) =
      T (defectInjection (translatedEmbedding edges n) W (realCoordinateEmbedding u)) := by
    rw [← hreal, defectInjection_real]
  ext i
  change (((weightedBlock edges W T n (realCoordinateEmbedding u) i).re : ℝ) : ℂ) = _
  have hcoord := congrArg (fun x : Field => x (edges i)) hr
  change star (T (defectInjection (translatedEmbedding edges n) W (realCoordinateEmbedding u)) (edges i)) = _ at hcoord
  have him := congrArg Complex.im hcoord
  simp only [Complex.star_def, Complex.conj_im] at him
  have hz : (T (defectInjection (translatedEmbedding edges n) W (realCoordinateEmbedding u)) (edges i)).im = 0 := by linarith
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, weightedBlock, ContinuousLinearMap.comp_apply,
      defectInjection_adjoint_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz]
    ring

theorem weightedBlock_real_inner_norm {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (hreal : ∀ x, T (star x) = star (T x))
    (n : Site) (u : EuclideanSpace ℝ (Fin N)) :
    ‖inner ℂ (realCoordinateEmbedding u)
      (weightedBlock edges W T n (realCoordinateEmbedding u))‖ =
      |inner ℝ u (realPartOperator (weightedBlock edges W T n) u)| := by
  rw [← weightedBlock_real edges W T hreal n u, realCoordinateEmbedding_inner,
    Complex.norm_real, Real.norm_eq_abs]

end Maxwell.Composition
