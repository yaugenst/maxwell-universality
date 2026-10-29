import Maxwell.Defect.CoherentCube
import Maxwell.Green.SourceProfile

/-! Exact Bloch profile of the physically assembled coherent cube source. -/
namespace Maxwell.Defect.ScalarDefect

open Spectral Spectral.Lattice Spectral.Bloch
open Maxwell.Green.PhysicalCompression

noncomputable section

theorem mFourier_apply_add (n : Site) (s t : Torus) :
    UnitAddTorus.mFourier n (s + t) =
      UnitAddTorus.mFourier n s * UnitAddTorus.mFourier n t := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem mFourier_apply_norm (n : Site) (t : Torus) :
    ‖UnitAddTorus.mFourier n t‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem mFourier_momentum (n : Site) (q : EuclideanSpace ℝ (Fin 3)) :
    UnitAddTorus.mFourier n (momentumTorus q) =
      Complex.exp (Complex.I * (inner ℝ q (periodVector n) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, momentumTorus,
    fourier_coe_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← Complex.exp_sum]
  congr 1
  rw [PiLp.inner_apply]
  simp only [periodVector, RCLike.inner_apply,
    conj_trivial, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  norm_num
  field_simp

/-- Actual lattice coefficients of `K_def w_L`, including the central
Bloch phase. -/
def coherentLatticeCoefficients (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Torus) (i : Fin (edges (cube L)).card) : ℂ :=
  (coordinateWeight (cube L) i : ℂ) *
    UnitAddTorus.mFourier (edgeCellEquiv (edgeEmbedding (cube L) i)).2 center *
    φ (edgeCellEquiv (edgeEmbedding (cube L) i)).1

theorem coherent_profile_regroup (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center t : Torus) (r : Edge20) :
    profile (edgeEmbedding (cube L)) (coherentLatticeCoefficients L φ center) t r =
      ∑ n ∈ supportPeriods L,
        (cellWeight L n r : ℂ) * UnitAddTorus.mFourier n center * φ r *
          UnitAddTorus.mFourier (-n) t := by
  classical
  unfold profile coherentLatticeCoefficients coordinateWeight
  rw [sum_cube_edgeCoordinates L
    (fun e => if r = (edgeCellEquiv e).1 then
      (weight (cube L) e : ℂ) * UnitAddTorus.mFourier (edgeCellEquiv e).2 center *
        φ (edgeCellEquiv e).1 * UnitAddTorus.mFourier (-(edgeCellEquiv e).2) t else 0)
    (fun e he => by simp [he])]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro n _
  simp [cellWeight]

theorem coherent_profile_local (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Torus) (q : EuclideanSpace ℝ (Fin 3)) (r : Edge20) :
    profile (edgeEmbedding (cube L)) (coherentLatticeCoefficients L φ center)
      (center + momentumTorus q) r =
      ∑ n ∈ supportPeriods L,
        Complex.exp (Complex.I * -(inner ℝ q (periodVector n) : ℂ)) * cellSource L φ n r := by
  rw [coherent_profile_regroup]
  apply Finset.sum_congr rfl
  intro n _
  rw [mFourier_apply_add]
  have hc : UnitAddTorus.mFourier n center * UnitAddTorus.mFourier (-n) center = 1 := by
    rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]
    rfl
  have hp : periodVector (-n) = -periodVector n := by
    ext j
    simp [periodVector]
  rw [mFourier_momentum, hp, inner_neg_right, Complex.ofReal_neg]
  change _ = _ * ((cellWeight L n r : ℂ) * φ r)
  calc
    _ = ((cellWeight L n r : ℂ) * φ r) *
        (UnitAddTorus.mFourier n center * UnitAddTorus.mFourier (-n) center) *
          Complex.exp (Complex.I * -(inner ℝ q (periodVector n) : ℂ)) := by ring
    _ = _ := by rw [hc]; ring

theorem coherent_profile_vector (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Torus) (q : EuclideanSpace ℝ (Fin 3)) :
    WithLp.toLp 2 (profile (edgeEmbedding (cube L))
      (coherentLatticeCoefficients L φ center) (center + momentumTorus q)) =
      ∑ n : ↥(supportPeriods L),
        Complex.exp (Complex.I * -(inner ℝ q (periodVector n) : ℂ)) • cellSource L φ n := by
  ext r
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_coe_sort (supportPeriods L) (fun n : Site =>
    Complex.exp (Complex.I * -(inner ℝ q (periodVector n) : ℂ)) * cellSource L φ n r)]
  exact coherent_profile_local L φ center q r

/-- The selected-band numerator in the actual Bloch integral is precisely
the coherent amplitude whose lower bound was proved from the cube geometry. -/
theorem coherent_profile_overlap (L : ℕ) (φ φ₀ : EuclideanSpace ℂ Edge20)
    (center : Torus) (q : EuclideanSpace ℝ (Fin 3)) :
    inner ℂ φ (WithLp.toLp 2 (profile (edgeEmbedding (cube L))
      (coherentLatticeCoefficients L φ₀ center) (center + momentumTorus q))) =
      coherentAmplitude L φ φ₀ q := by
  rw [coherent_profile_vector]
  rfl

theorem coherent_finiteField (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Torus) :
    finiteField (edgeEmbedding (cube L)) (coherentLatticeCoefficients L φ center) =
      injection (cube L) (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n center)) := by
  change Maxwell.Target.sequenceExtension (edgeEmbedding (cube L))
    (WithLp.toLp 2 (coherentLatticeCoefficients L φ center)) =
      Maxwell.Target.sequenceExtension (edgeEmbedding (cube L))
        (complexSqrtWeightOperator (coordinateWeight (cube L))
          (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n center)))
  congr 1
  ext i
  rw [complexSqrtWeightOperator_apply]
  change (coordinateWeight (cube L) i : ℂ) * _ * _ =
    (Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
      ((Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) * _ * _)
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt]
  · simp only [Complex.ofReal_ratCast]
  · have h := (coordinateWeight_bounds (cube L) i).1
    exact_mod_cast (show (0 : ℚ) ≤ coordinateWeight (cube L) i by linarith)

theorem mFourier_apply_neg (n : Site) (t : Torus) :
    UnitAddTorus.mFourier n (-t) = UnitAddTorus.mFourier (-n) t := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, smul_neg, neg_smul]

theorem mFourier_real_at_trim (n : Site) (center : Torus)
    (hcenter : center + center = 0) :
    (UnitAddTorus.mFourier n center).im = 0 := by
  have hn : -center = center := (eq_neg_of_add_eq_zero_left hcenter).symm
  have heq : star (UnitAddTorus.mFourier n center) = UnitAddTorus.mFourier n center := by
    rw [Complex.star_def, ← UnitAddTorus.mFourier_neg, ← mFourier_apply_neg, hn]
  have him := congrArg Complex.im heq
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- Every conventional momentum with integer multiples of pi is a
time-reversal fixed torus point, including `(pi,pi,-pi)`. -/
theorem momentumTorus_trim (k : Site) :
    momentumTorus (fun j => Real.pi * (k j : ℝ)) +
      momentumTorus (fun j => Real.pi * (k j : ℝ)) = 0 := by
  ext j
  change ((Real.pi * (k j : ℝ) / (2 * Real.pi) : ℝ) : UnitAddCircle) +
    ((Real.pi * (k j : ℝ) / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0
  rw [← AddCircle.coe_add]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨k j, ?_⟩
  simp only [zsmul_eq_mul, mul_one]
  field_simp
  ring

theorem coherentCoordinates_real_at_trim (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ∀ r, (φ r).im = 0) (center : Torus) (hcenter : center + center = 0) :
    realCoordinateEmbedding (realCoordinatePart
      (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n center))) =
      coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n center) := by
  ext i
  apply Complex.ext
  · rfl
  · simp [coherentCoordinates, Complex.mul_im, hφ,
      mFourier_real_at_trim _ center hcenter]

/-- The coherent vector is the actual edge-projector source vector,
including the physical square-root weights and central Fourier phases. -/
theorem sourceLeft_coherentCoordinates (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Fin 3 → ℝ) :
    Green.SourceProfile.sourceLeft (edgeEmbedding (cube L)) (coordinateWeight (cube L))
      (Green.SourceProfile.realMomentum center) φ =
      coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n (momentumTorus center)) := by
  classical
  ext i
  simp only [Green.SourceProfile.sourceLeft, Green.SourceProfile.rectangularMap_apply,
    Matrix.mulVec, dotProduct, Green.SourceProfile.leftMatrix,
    Green.SourceProfile.phase_real, coherentCoordinates]
  change (∑ r, (if r = (edgeCellEquiv (edgeEmbedding (cube L) i)).1 then
    (Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
      UnitAddTorus.mFourier (edgeCellEquiv (edgeEmbedding (cube L) i)).2
        (momentumTorus center) else 0) * φ r) = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sourceRight_adjoint_coherentCoordinates (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Fin 3 → ℝ) :
    (Green.SourceProfile.sourceRight (edgeEmbedding (cube L)) (coordinateWeight (cube L))
      (Green.SourceProfile.realMomentum center)).adjoint φ =
      coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n (momentumTorus center)) := by
  rw [← Green.SourceProfile.sourceLeft_real_adjoint]
  exact sourceLeft_coherentCoordinates L φ center

theorem coherent_sourceCompression_rankOne (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Fin 3 → ℝ) :
    sourceCompression (Green.SourceProfile.sourceRight (edgeEmbedding (cube L))
      (coordinateWeight (cube L)) (Green.SourceProfile.realMomentum center))
      (InnerProductSpace.rankOne ℂ φ φ) =
      InnerProductSpace.rankOne ℂ
        (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n (momentumTorus center)))
        (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n (momentumTorus center))) := by
  rw [sourceCompression_rankOne, sourceRight_adjoint_coherentCoordinates]

/-- The overlap selected by the real rank-one branch is exactly the
physical selected-band numerator overlap used by the Green readout. -/
theorem coherent_source_overlap_real (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ∀ r, (φ r).im = 0) (center : Fin 3 → ℝ)
    (hcenter : momentumTorus center + momentumTorus center = 0)
    (u : EuclideanSpace ℝ (Fin (edges (cube L)).card)) :
    inner ℂ φ (Green.SourceProfile.sourceRight (edgeEmbedding (cube L))
      (coordinateWeight (cube L)) (Green.SourceProfile.realMomentum center)
        (realCoordinateEmbedding u)) =
      (inner ℝ (realCoordinatePart (coherentCoordinates L φ
        (fun n => UnitAddTorus.mFourier n (momentumTorus center)))) u : ℂ) := by
  rw [← ContinuousLinearMap.adjoint_inner_left, sourceRight_adjoint_coherentCoordinates]
  rw [← coherentCoordinates_real_at_trim L φ hφ (momentumTorus center) hcenter,
    realCoordinateEmbedding_inner]
  simp only [realCoordinatePart_embedding]

theorem coherent_source_overlap_nonzero (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ∀ r, (φ r).im = 0) (center : Fin 3 → ℝ)
    (hcenter : momentumTorus center + momentumTorus center = 0)
    (u : EuclideanSpace ℝ (Fin (edges (cube L)).card))
    (hoverlap : inner ℝ (realCoordinatePart (coherentCoordinates L φ
      (fun n => UnitAddTorus.mFourier n (momentumTorus center)))) u ≠ 0) :
    inner ℂ φ (Green.SourceProfile.sourceRight (edgeEmbedding (cube L))
      (coordinateWeight (cube L)) (Green.SourceProfile.realMomentum center)
        (realCoordinateEmbedding u)) ≠ 0 := by
  rw [coherent_source_overlap_real L φ hφ center hcenter u]
  exact_mod_cast hoverlap

end
end Maxwell.Defect.ScalarDefect
