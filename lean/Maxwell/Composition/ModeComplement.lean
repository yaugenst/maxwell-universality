import Maxwell.Composition.OrthogonalModes
import Maxwell.Composition.LocalBlocks
import Maxwell.Composition.PhysicalPlatform

/-! The orthogonal complement of repeated local modes is the Euclidean direct
sum of the local complements. Its inverse bound is independent of the number
of sites. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators InnerProduct

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

abbrev ModeLocalComplement (q : EuclideanSpace ℝ κ) :=
  (Submodule.span ℝ ({q} : Set (EuclideanSpace ℝ κ)))ᗮ

theorem blockInjection_adjoint_coordinate (q : EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    (blockInjection q).adjoint x i = inner ℝ q (blockCoordinate x i) := by
  have h := blockReadout_apply q (fun _ : ι => (1 : ℝ)) x i
  simpa [blockReadout, PiLp.inner_apply, blockCoordinate, mul_comm] using h

theorem mem_modeComplement_iff (q : EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) :
    x ∈ ModeComplement (ι := ι) q ↔
      ∀ i, blockCoordinate x i ∈ ModeLocalComplement q := by
  change x ∈ (blockInjection q).rangeᗮ ↔ _
  rw [ContinuousLinearMap.orthogonal_range]
  change (blockInjection q).adjoint x = 0 ↔ _
  constructor
  · intro h i
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [← blockInjection_adjoint_coordinate q x i, h]
    rfl
  · intro h
    ext i
    rw [blockInjection_adjoint_coordinate]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (h i)

def modeLocalCoordinate (q : EuclideanSpace ℝ κ)
    (x : ModeComplement (ι := ι) q) (i : ι) : ModeLocalComplement q :=
  ⟨blockCoordinate x.val i, (mem_modeComplement_iff q x.val).mp x.property i⟩

@[simp] theorem modeLocalCoordinate_add (q : EuclideanSpace ℝ κ)
    (x y : ModeComplement (ι := ι) q) (i : ι) :
    modeLocalCoordinate q (x + y) i = modeLocalCoordinate q x i +
      modeLocalCoordinate q y i := by
  apply Subtype.ext
  exact blockCoordinate_add x.val y.val i

@[simp] theorem modeLocalCoordinate_smul (q : EuclideanSpace ℝ κ)
    (a : ℝ) (x : ModeComplement (ι := ι) q) (i : ι) :
    modeLocalCoordinate q (a • x) i = a • modeLocalCoordinate q x i := by
  apply Subtype.ext
  exact blockCoordinate_smul a x.val i

def modeComplementBlocksLinear (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q →L[ℝ] ModeLocalComplement q) :
    ModeComplement (ι := ι) q →ₗ[ℝ] ModeComplement (ι := ι) q where
  toFun x := ⟨WithLp.toLp 2 (fun ij => (A ij.1 (modeLocalCoordinate q x ij.1)).val ij.2), by
    apply (mem_modeComplement_iff q _).mpr
    intro i
    change (A i (modeLocalCoordinate q x i)).val ∈ ModeLocalComplement q
    exact (A i (modeLocalCoordinate q x i)).property⟩
  map_add' x y := by
    apply Subtype.ext
    ext ij
    simp
  map_smul' a x := by
    apply Subtype.ext
    ext ij
    simp

def modeComplementBlocks (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q →L[ℝ] ModeLocalComplement q) :
    ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q :=
  (modeComplementBlocksLinear q A).toContinuousLinearMap

@[simp] theorem modeComplementBlocks_coordinate (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q →L[ℝ] ModeLocalComplement q)
    (x : ModeComplement (ι := ι) q) (i : ι) :
    modeLocalCoordinate q (modeComplementBlocks q A x) i =
      A i (modeLocalCoordinate q x i) := by
  apply Subtype.ext
  ext j
  rfl

theorem modeComplement_norm_sq (q : EuclideanSpace ℝ κ)
    (x : ModeComplement (ι := ι) q) :
    ‖x‖ ^ 2 = ∑ i, ‖modeLocalCoordinate q x i‖ ^ 2 :=
  euclidean_norm_sq_blocks x.val

theorem modeComplementBlocks_norm_le (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q →L[ℝ] ModeLocalComplement q)
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ i, ‖A i‖ ≤ R) :
    ‖modeComplementBlocks q A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  rw [modeComplement_norm_sq, mul_pow, modeComplement_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [modeComplementBlocks_coordinate, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((A i).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

theorem modeLocalCoordinate_ext (q : EuclideanSpace ℝ κ)
    {x y : ModeComplement (ι := ι) q}
    (h : ∀ i, modeLocalCoordinate q x i = modeLocalCoordinate q y i) : x = y := by
  apply Subtype.ext
  ext ⟨i, j⟩
  exact congrArg (fun z : ModeLocalComplement q => z.val j) (h i)

theorem modeComplementBlocks_inverse_left (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (x : ModeComplement (ι := ι) q) :
    modeComplementBlocks q (fun i => (A i : ModeLocalComplement q →L[ℝ]
      ModeLocalComplement q))
      (modeComplementBlocks q (fun i => ((A i).symm : ModeLocalComplement q →L[ℝ]
        ModeLocalComplement q)) x) = x := by
  apply modeLocalCoordinate_ext q
  intro i
  simp

theorem modeComplementBlocks_inverse_right (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (x : ModeComplement (ι := ι) q) :
    modeComplementBlocks q (fun i => ((A i).symm : ModeLocalComplement q →L[ℝ]
      ModeLocalComplement q))
      (modeComplementBlocks q (fun i => (A i : ModeLocalComplement q →L[ℝ]
        ModeLocalComplement q)) x) = x := by
  apply modeLocalCoordinate_ext q
  intro i
  simp

/-- The actual direct sum equivalence on the orthogonal complement of the
repeated mode range. -/
def modeComplementBlockEquiv (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q) :
    ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q :=
  ContinuousLinearEquiv.equivOfInverse'
    (modeComplementBlocks q (fun i => (A i : ModeLocalComplement q →L[ℝ]
      ModeLocalComplement q)))
    (modeComplementBlocks q (fun i => ((A i).symm : ModeLocalComplement q →L[ℝ]
      ModeLocalComplement q)))
    (ContinuousLinearMap.ext (modeComplementBlocks_inverse_left q A))
    (ContinuousLinearMap.ext (modeComplementBlocks_inverse_right q A))

@[simp] theorem modeComplementBlockEquiv_coordinate (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (x : ModeComplement (ι := ι) q) (i : ι) :
    modeLocalCoordinate q (modeComplementBlockEquiv q A x) i =
      A i (modeLocalCoordinate q x i) :=
  modeComplementBlocks_coordinate q _ x i

/-- There is no cardinality factor: the Euclidean direct sum inherits the
same inverse bound as each local complement. -/
theorem modeComplementBlockEquiv_inverse_norm_le (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i, ‖((A i).symm : ModeLocalComplement q →L[ℝ]
      ModeLocalComplement q)‖ ≤ R) :
    ‖((modeComplementBlockEquiv q A).symm : ModeComplement (ι := ι) q →L[ℝ]
      ModeComplement (ι := ι) q)‖ ≤ R := by
  rw [modeComplementBlockEquiv, ContinuousLinearEquiv.symm_equivOfInverse',
    ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse']
  exact modeComplementBlocks_norm_le q
    (fun i => ((A i).symm : ModeLocalComplement q →L[ℝ] ModeLocalComplement q)) R hR hA

theorem modeComplementBlockEquiv_operator (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (μ : ℝ) (G : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (hA : ∀ i (x : ModeLocalComplement q),
      (A i x : EuclideanSpace ℝ κ) = μ • (x : EuclideanSpace ℝ κ) - G i x)
    (x : ModeComplement (ι := ι) q) :
    modeComplementInclusion q (modeComplementBlockEquiv q A x) =
      μ • modeComplementInclusion q x - diagonalBlocks G (modeComplementInclusion q x) := by
  ext ⟨i, j⟩
  have h := congrArg (fun z : EuclideanSpace ℝ κ => z j)
    (hA i (modeLocalCoordinate q x i))
  exact h

/-- The constructed inverse belongs to the actual compressed operator. -/
theorem modeComplementBlockEquiv_compression (q : EuclideanSpace ℝ κ)
    (A : ι → ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (μ : ℝ) (G : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (hA : ∀ i (x : ModeLocalComplement q),
      (A i x : EuclideanSpace ℝ κ) = μ • (x : EuclideanSpace ℝ κ) - G i x) :
    (modeComplementBlockEquiv q A : ModeComplement (ι := ι) q →L[ℝ]
      ModeComplement (ι := ι) q) =
      (modeComplementProjection q).comp
        ((μ • 1 - diagonalBlocks G).comp (modeComplementInclusion q)) := by
  apply ContinuousLinearMap.ext
  intro x
  change modeComplementBlockEquiv q A x = modeComplementProjection q
    (μ • modeComplementInclusion q x - diagonalBlocks G (modeComplementInclusion q x))
  rw [← modeComplementBlockEquiv_operator q A μ G hA x,
    modeComplementProjection_inclusion]

namespace PhysicalPlatform

/-- Repeating the fixed physical local complement at every decorated site. -/
def modeComplementEquiv (P : PhysicalPlatform) :
    ModeComplement (ι := ι) P.mode ≃L[ℝ] ModeComplement (ι := ι) P.mode :=
  modeComplementBlockEquiv P.mode (fun _ => P.complement)

theorem modeComplementEquiv_inverse_norm_le (P : PhysicalPlatform) :
    ‖((P.modeComplementEquiv (ι := ι)).symm :
      ModeComplement (ι := ι) P.mode →L[ℝ] ModeComplement (ι := ι) P.mode)‖ ≤
      1 / (P.defectGap : ℝ) := by
  apply modeComplementBlockEquiv_inverse_norm_le
  · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast P.defectGap_pos))
  · intro i
    exact P.complement_inverse_bound

theorem modeComplementEquiv_operator (P : PhysicalPlatform)
    (x : ModeComplement (ι := ι) P.mode) :
    modeComplementInclusion P.mode (P.modeComplementEquiv x) =
      P.eigenvalue • modeComplementInclusion P.mode x -
        diagonalBlocks (fun _ : ι => physicalGreenBlock P.defect
          (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)
          (modeComplementInclusion P.mode x) := by
  exact modeComplementBlockEquiv_operator P.mode (fun _ => P.complement)
    P.eigenvalue _ (fun _ => P.complement_operator) x

theorem modeComplementEquiv_compression (P : PhysicalPlatform) :
    (P.modeComplementEquiv (ι := ι) : ModeComplement (ι := ι) P.mode →L[ℝ]
      ModeComplement (ι := ι) P.mode) =
      (modeComplementProjection P.mode).comp
        ((P.eigenvalue • 1 - diagonalBlocks (fun _ : ι => physicalGreenBlock P.defect
          (P.bulk.symm : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field) 0)).comp
            (modeComplementInclusion P.mode)) := by
  exact modeComplementBlockEquiv_compression P.mode (fun _ => P.complement)
    P.eigenvalue _ (fun _ => P.complement_operator)

end PhysicalPlatform

end Maxwell.Composition
