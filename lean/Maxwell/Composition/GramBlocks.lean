import Maxwell.Composition.RealGram
import Maxwell.Composition.TranslationBlocks
import Maxwell.Composition.Interactions

/-! Exact local blocks of the complete weighted infinite compression.
This identifies the same physical sources used in the finite layout and
in the periodic Green integral. -/
noncomputable section
namespace Maxwell.Composition.FiniteGram
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators InnerProduct

variable {B : Target.Box} {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {blocks : ι → Finset B.Cell} (layout : DefectLayout (κ := Fin N) blocks)

def localEmbedding (i : ι) : Fin N ↪ Edge :=
  ⟨fun k => unionEmbedding layout (i, k), fun _a _b h =>
    (Prod.mk.inj ((unionEmbedding layout).injective h)).2⟩

def blockInsertion (i : ι) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (ι × Fin N) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun jk => if jk.1 = i then x jk.2 else 0
      map_add' := by intros; ext jk; dsimp; split_ifs <;> simp
      map_smul' := by intros; ext jk; dsimp; split_ifs <;> simp }

@[simp] theorem blockInsertion_apply (i : ι) (x : EuclideanSpace ℂ (Fin N)) (j : ι) (k : Fin N) :
    blockInsertion i x (j, k) = if j = i then x k else 0 := rfl

@[simp] theorem blockInsertion_adjoint (i : ι) (x : EuclideanSpace ℂ (ι × Fin N)) (k : Fin N) :
    (blockInsertion i).adjoint x k = x (i, k) := by
  have h := ContinuousLinearMap.adjoint_inner_right (blockInsertion i) (EuclideanSpace.single k 1) x
  simpa [PiLp.inner_apply, Fintype.sum_prod_type, blockInsertion_apply, apply_ite] using h

def unionInjection : EuclideanSpace ℂ (ι × Fin N) →L[ℂ] Field :=
  (Target.sequenceExtension (unionEmbedding layout)).toContinuousLinearMap.comp (sqrtWeight layout)

theorem infinite_eq_compression (T : Field →L[ℂ] Field) :
    infinite layout T = (unionInjection layout).adjoint.comp (T.comp (unionInjection layout)) := by
  rw [unionInjection, ContinuousLinearMap.adjoint_comp, sqrtWeight_selfAdjoint]
  rfl

/-- Selecting a block of the whole-union injection gives its actual weighted
finite lattice source, with the exact shared prototype coefficients. -/
theorem unionInjection_block (W : Fin N → ℚ) (hw : ∀ i k, layout.weight (i, k) = W k) (i : ι) :
    (unionInjection layout).comp (blockInsertion i) =
      Maxwell.Defect.defectInjection (localEmbedding layout i) W := by
  ext x e
  change Target.sequenceExtensionLinear (unionEmbedding layout)
    (sqrtWeight layout (blockInsertion i x)) e =
    Target.sequenceExtensionLinear (localEmbedding layout i) (Maxwell.Defect.complexSqrtWeightOperator W x) e
  rw [Target.sequenceExtensionLinear_apply, Target.sequenceExtensionLinear_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [sqrtWeight_apply, blockInsertion_apply, ite_true, DefectLayout.sqrtWeight,
      hw, Maxwell.Defect.complexSqrtWeightOperator_apply]
    rfl
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro k _
    simp [sqrtWeight_apply, blockInsertion_apply, hji]
  · simp

/-- A block of the full physical Gram operator is the compression between
its two actual translated prototype injections. -/
theorem infinite_local_block (W : Fin N → ℚ) (hw : ∀ i k, layout.weight (i, k) = W k)
    (T : Field →L[ℂ] Field) (i j : ι) :
    (blockInsertion i).adjoint.comp ((infinite layout T).comp (blockInsertion j)) =
      (Maxwell.Defect.defectInjection (localEmbedding layout i) W).adjoint.comp
        (T.comp (Maxwell.Defect.defectInjection (localEmbedding layout j) W)) := by
  rw [infinite_eq_compression]
  have hi := congrArg ContinuousLinearMap.adjoint (unionInjection_block layout W hw i)
  rw [ContinuousLinearMap.adjoint_comp] at hi
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← unionInjection_block layout W hw j]
  have := congrArg (fun C => C.comp (T.comp ((unionInjection layout).comp (blockInsertion j)))) hi
  simpa only [ContinuousLinearMap.comp_assoc] using this

/-- For actual period-preserving placements, the local Gram block is the
same `weightedBlock` appearing in the physical Fourier representation. -/
theorem infinite_periodic_block (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (hw : ∀ i k, layout.weight (i, k) = W k) (anchors : ι → Site)
    (he : ∀ i, localEmbedding layout i = TranslationBlocks.placedEmbedding edges (anchors i))
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℂ) (i j : ι) :
    (blockInsertion i).adjoint.comp
      ((infinite layout (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1))).comp
        (blockInsertion j)) =
      Green.PhysicalCompression.weightedBlock edges W
        (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1)) (anchors i - anchors j) := by
  rw [infinite_local_block layout W hw, he i, he j]
  exact TranslationBlocks.inverse_placedBlock edges W m K hK hm z (anchors i) (anchors j)

theorem sum_blockInsertion (x : EuclideanSpace ℂ (ι × Fin N)) :
    (∑ i : ι, blockInsertion i (WithLp.toLp 2 fun k => x (i, k))) = x := by
  ext ij
  rcases ij with ⟨i, k⟩
  simp [blockInsertion_apply]

/-- Block reconstruction is exact on the complete real union, including
all off-diagonal blocks. -/
theorem realOperator_blocks (T : EuclideanSpace ℂ (ι × Fin N) →L[ℂ]
    EuclideanSpace ℂ (ι × Fin N)) :
    realOperator T = interactionOperator (fun i j => Maxwell.Defect.realPartOperator
      ((blockInsertion i).adjoint.comp (T.comp (blockInsertion j)))) := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : (∑ i : ι, blockInsertion i (euclideanComplexLift (blockCoordinate x i))) =
      euclideanComplexLift x := by
    simpa only [euclideanComplexLift, blockCoordinate, PiLp.toLp_apply] using
      sum_blockInsertion (euclideanComplexLift x)
  have ht := congrArg T hx
  rw [map_sum] at ht
  ext ij
  rcases ij with ⟨i, k⟩
  change (T (euclideanComplexLift x) (i, k)).re =
    (∑ j, Maxwell.Defect.realPartOperator
      ((blockInsertion i).adjoint.comp (T.comp (blockInsertion j))) (blockCoordinate x j)) k
  rw [← ht]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Complex.re_sum, Maxwell.Defect.realPartOperator_apply,
    Maxwell.Defect.realCoordinatePart_apply, ContinuousLinearMap.comp_apply, blockInsertion_adjoint]
  rfl

end Maxwell.Composition.FiniteGram
