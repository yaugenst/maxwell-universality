import Maxwell.Composition.ModeComplement

/-! Exact bright/complement splitting of the local scalar diagonal baseline.
The baseline contains the literal local Green block; its mixed blocks vanish
because the selected mode is an eigenvector of this symmetric block. -/

noncomputable section

namespace Maxwell.Composition

open scoped InnerProduct

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Local blocks with scalar inverse strength `d i` and common local Green map. -/
def modeBaseline (d : ι → ℝ) (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  diagonalBlocks (fun i => d i • 1 - G)

@[simp] theorem modeBaseline_coordinate (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockCoordinate (modeBaseline d G x) i =
      d i • blockCoordinate x i - G (blockCoordinate x i) := by
  simp [modeBaseline]

@[simp] theorem blockCoordinate_injection (q : EuclideanSpace ℝ κ)
    (g : EuclideanSpace ℝ ι) (i : ι) :
    blockCoordinate (blockInjection q g) i = g i • q := by
  ext j
  simp [blockCoordinate, mul_comm]

theorem modeBaseline_injection (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (q : EuclideanSpace ℝ κ) (μ : ℝ) (heigen : G q = μ • q) :
    (modeBaseline d G).comp (blockInjection q) =
      (blockInjection q).comp (blockDiagonal (fun i => d i - μ)) := by
  apply ContinuousLinearMap.ext
  intro g
  ext ⟨i, j⟩
  have h := congrArg (fun z : EuclideanSpace ℝ κ => z j)
    (modeBaseline_coordinate d G (blockInjection q g) i)
  rw [blockCoordinate_injection, map_smul, heigen] at h
  simpa [blockCoordinate, sub_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using h

/-- The actual bright diagonal is the inverse strength minus the local
mode eigenvalue. -/
theorem modeBaseline_bright (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (μ : ℝ) (heigen : G q = μ • q) :
    (blockInjection q).adjoint.comp ((modeBaseline d G).comp (blockInjection q)) =
      blockDiagonal (fun i => d i - μ) := by
  rw [modeBaseline_injection d G q μ heigen, ← ContinuousLinearMap.comp_assoc,
    blockInjection_adjoint_comp_self q hq]
  rfl

/-- Symmetry and the exact local eigenvector remove the complement-to-bright
mixed block. -/
theorem modeBaseline_bright_complement_zero (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (hG : G.toLinearMap.IsSymmetric) (q : EuclideanSpace ℝ κ)
    (μ : ℝ) (heigen : G q = μ • q) :
    (blockInjection q).adjoint.comp
      ((modeBaseline d G).comp (modeComplementInclusion q)) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  change (blockInjection q).adjoint
    (modeBaseline d G (modeComplementInclusion q x)) i = 0
  rw [blockInjection_adjoint_coordinate, modeBaseline_coordinate]
  have horth : inner ℝ q (blockCoordinate (modeComplementInclusion q x) i) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (modeLocalCoordinate q x i).property
  have hsym := hG q (blockCoordinate (modeComplementInclusion q x) i)
  change inner ℝ (G q) _ = inner ℝ q (G _) at hsym
  rw [inner_sub_right, inner_smul_right, ← hsym, heigen, inner_smul_left]
  simp [horth]

/-- The bright-to-complement mixed block also vanishes exactly. -/
theorem modeBaseline_complement_bright_zero (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (μ : ℝ) (heigen : G q = μ • q) :
    (modeComplementProjection q).comp
      ((modeBaseline d G).comp (blockInjection q)) = 0 := by
  rw [modeBaseline_injection d G q μ heigen]
  apply ContinuousLinearMap.ext
  intro g
  simp [hq]

/-- Scalar shifts restricted to the actual repeated-mode complement. -/
def modeComplementScalar (q : EuclideanSpace ℝ κ) (d : ι → ℝ) :
    ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q :=
  modeComplementBlocks q (fun i => d i • 1)

@[simp] theorem modeComplementScalar_coordinate (q : EuclideanSpace ℝ κ)
    (d : ι → ℝ) (x : ModeComplement (ι := ι) q) (i : ι) :
    modeLocalCoordinate q (modeComplementScalar q d x) i =
      d i • modeLocalCoordinate q x i := by
  simp [modeComplementScalar]

theorem modeComplementScalar_norm_le (q : EuclideanSpace ℝ κ)
    (d : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hd : ∀ i, |d i| ≤ R) :
    ‖modeComplementScalar q d‖ ≤ R := by
  apply modeComplementBlocks_norm_le q _ R hR
  intro i
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  change ‖d i • x‖ ≤ R * ‖x‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hd i) (norm_nonneg x)

/-- The varying inverse strengths contribute only their scalar deviation
from the fixed local eigenvalue to the complementary baseline. -/
theorem modeBaseline_complement (d : ι → ℝ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (q : EuclideanSpace ℝ κ) (μ : ℝ)
    (A : ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (hA : ∀ x : ModeLocalComplement q,
      (A x : EuclideanSpace ℝ κ) = μ • (x : EuclideanSpace ℝ κ) - G x) :
    (modeComplementProjection q).comp
      ((modeBaseline d G).comp (modeComplementInclusion q)) =
        (modeComplementBlockEquiv q (fun _ : ι => A) :
          ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q) +
          modeComplementScalar q (fun i => d i - μ) := by
  apply ContinuousLinearMap.ext
  intro x
  have h : modeBaseline d G (modeComplementInclusion q x) =
      modeComplementInclusion q
        (modeComplementBlockEquiv q (fun _ : ι => A) x +
          modeComplementScalar q (fun i => d i - μ) x) := by
    ext ⟨i, j⟩
    have hlocal := congrArg (fun z : EuclideanSpace ℝ κ => z j)
      (hA (modeLocalCoordinate q x i))
    change d i * x.val (i, j) - G (blockCoordinate x.val i) j =
      (A (modeLocalCoordinate q x i)).val j + (d i - μ) * x.val (i, j)
    change (A (modeLocalCoordinate q x i)).val j =
      μ * x.val (i, j) - G (blockCoordinate x.val i) j at hlocal
    rw [hlocal]
    ring
  change modeComplementProjection q (modeBaseline d G (modeComplementInclusion q x)) = _
  rw [h, modeComplementProjection_inclusion]
  rfl

namespace PhysicalPlatform

/-- Exact bright scalar diagonal for the physical local Green block. -/
theorem modeBaseline_bright (P : PhysicalPlatform) (d : ι → ℝ) :
    (blockInjection P.mode).adjoint.comp
      ((modeBaseline d (physicalGreenBlock P.defect
        (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)).comp
          (blockInjection P.mode)) = blockDiagonal (fun i => d i - P.eigenvalue) :=
  Maxwell.Composition.modeBaseline_bright d _ P.mode P.mode_unit P.eigenvalue P.mode_equation

theorem modeBaseline_bright_complement_zero (P : PhysicalPlatform) (d : ι → ℝ) :
    (blockInjection P.mode).adjoint.comp
      ((modeBaseline d (physicalGreenBlock P.defect
        (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)).comp
          (modeComplementInclusion P.mode)) = 0 :=
  Maxwell.Composition.modeBaseline_bright_complement_zero d _ P.local_symmetric P.mode
    P.eigenvalue P.mode_equation

theorem modeBaseline_complement_bright_zero (P : PhysicalPlatform) (d : ι → ℝ) :
    (modeComplementProjection P.mode).comp
      ((modeBaseline d (physicalGreenBlock P.defect
        (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)).comp
          (blockInjection P.mode)) = 0 :=
  Maxwell.Composition.modeBaseline_complement_bright_zero d _ P.mode P.mode_unit
    P.eigenvalue P.mode_equation

theorem modeBaseline_complement (P : PhysicalPlatform) (d : ι → ℝ) :
    (modeComplementProjection P.mode).comp
      ((modeBaseline d (physicalGreenBlock P.defect
        (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)).comp
          (modeComplementInclusion P.mode)) =
        (P.modeComplementEquiv (ι := ι) : ModeComplement (ι := ι) P.mode →L[ℝ]
          ModeComplement (ι := ι) P.mode) +
          modeComplementScalar P.mode (fun i => d i - P.eigenvalue) :=
  Maxwell.Composition.modeBaseline_complement d _ P.mode P.eigenvalue P.complement
    P.complement_operator

end PhysicalPlatform

end Maxwell.Composition
