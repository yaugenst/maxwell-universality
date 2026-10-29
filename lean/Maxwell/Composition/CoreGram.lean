import Maxwell.Composition.RealGram

/-! Exact weighted core from the actual scalar strengths and finite Gram.
No separately supplied Birman--Schwinger matrix is used. -/
noncomputable section
namespace Maxwell.Composition.FiniteGram

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {blocks : ι → Finset B.Cell} (layout : DefectLayout (κ := κ) blocks)

omit [DecidableEq ι] [DecidableEq κ] in
theorem weighted_strength_inverse (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) :
    (layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).comp
      (((layout.strengthEquiv v hv).symm : EuclideanSpace ℝ (ι × κ) →L[ℝ]
        EuclideanSpace ℝ (ι × κ)).comp
          (layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))) =
      blockDiagonal (fun ij => ((v ij.1 : ℝ))⁻¹) := by
  ext x ij
  change layout.sqrtWeight ij * (((v ij.1 * layout.weight ij : ℚ) : ℝ)⁻¹ *
    (layout.sqrtWeight ij * x ij)) = (v ij.1 : ℝ)⁻¹ * x ij
  have hw : 0 < (layout.weight ij : ℝ) := by
    have h := (layout.weight_bounds ij).1
    have hq : (0 : ℚ) < layout.weight ij := lt_of_lt_of_le (by norm_num) h
    exact_mod_cast hq
  have hs : layout.sqrtWeight ij * layout.sqrtWeight ij = (layout.weight ij : ℝ) :=
    Real.mul_self_sqrt hw.le
  rw [Rat.cast_mul, mul_inv_rev]
  calc
    _ = (v ij.1 : ℝ)⁻¹ * ((layout.weight ij : ℝ)⁻¹ *
        (layout.sqrtWeight ij * layout.sqrtWeight ij)) * x ij := by ring
    _ = _ := by rw [hs, inv_mul_cancel₀ hw.ne', mul_one]

/-- The complete physical weighted core is exactly diagonal inverse strength
minus the real part of the actual finite weighted background compression. -/
theorem weighted_core_eq (M : Matrix B.Edge B.Edge ℝ)
    (A : EuclideanSpace ℂ B.Edge ≃L[ℂ] EuclideanSpace ℂ B.Edge)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (hA : (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map fun a => (a : ℂ)))
    (hK : (K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) M)
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) :
    weightedBirmanSchwinger K (layout.strengthEquiv v hv) layout.weightEquiv
      (coordinateRestriction layout.pick) (coordinateExtension layout.pick) =
      blockDiagonal (fun ij => (v ij.1 : ℝ)⁻¹) -
        realOperator (finite layout (A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)) := by
  rw [real_finite_eq layout M A K hA hK, ← weighted_strength_inverse layout v hv]
  ext x
  simp [weightedBirmanSchwinger, ContinuousLinearMap.comp_apply]

end Maxwell.Composition.FiniteGram
