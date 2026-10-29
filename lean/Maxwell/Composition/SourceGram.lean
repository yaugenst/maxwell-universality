import Maxwell.Composition.GramBlocks
import Maxwell.Composition.BasisDefectBounds

/-! The actual routed, integer-basis, scalar-cell layout binds the full
finite weighted Gram operator to the genuine periodic Green blocks. -/
noncomputable section
namespace Maxwell.Composition.SourceGram
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.FiniteGram
open scoped BigOperators

variable (S : Source.SparseSystem) (precision : ℕ) (B : Matrix Direction Direction ℤ)
variable (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
variable (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
local instance : DecidableEq (SourceRouting.Vertex S precision) := Classical.decEq _

abbrev layout := BasisDefectLayout.layout S precision B hB D macroSpacing buffer hspacing

/-- Both the block coordinates and weights are derived from the same
emitted prototype cells; this is the physical Green source identification. -/
theorem local_embedding (i : SourceRouting.Vertex S precision) :
    FiniteGram.localEmbedding (layout S precision B hB D macroSpacing buffer hspacing) i =
      TranslationBlocks.placedEmbedding (ScalarDefect.edgeEmbedding D)
        (BasisDefectLayout.conventionalAnchor S precision B D macroSpacing buffer i) := by
  apply Function.Embedding.ext
  intro k
  change Target.latticeEdge _
    ((BasisDefectLayout.layout S precision B hB D macroSpacing buffer hspacing).pick (i, k)) = _
  rw [BasisDefectLayout.lattice_pick, TranslationBlocks.placedEmbedding_apply]
  simp only [TranslatedStencil.edge, add_comm]
  rfl

/-- Exact full-union reconstruction by physical periodic Green blocks. -/
theorem infinite_blocks (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℂ) :
    realOperator (infinite (layout S precision B hB D macroSpacing buffer hspacing)
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1))) =
      interactionOperator (fun i j => Maxwell.Defect.realPartOperator
        (Green.PhysicalCompression.weightedBlock (ScalarDefect.edgeEmbedding D)
          (ScalarDefect.coordinateWeight D)
          (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1))
          ((macroSpacing : ℤ) • B.mulVec
            (SourceDefectLayout.position S precision i - SourceDefectLayout.position S precision j)))) := by
  rw [realOperator_blocks]
  congr 1
  funext i j
  rw [infinite_periodic_block _ (ScalarDefect.edgeEmbedding D) (ScalarDefect.coordinateWeight D)
    (fun i k => BasisDefectLayout.shared_weight S precision B hB D macroSpacing buffer hspacing (i, k))
    (BasisDefectLayout.conventionalAnchor S precision B D macroSpacing buffer)
    (local_embedding S precision B hB D macroSpacing buffer hspacing)]
  rw [BasisDefectLayout.anchor_difference]

/-- The actual whole-union margin, in the real metric used by the Green
boundary theorem. It follows from the constructed box, even after B. -/
theorem union_margin (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card)
    (k : Direction) :
    (buffer : ℝ) ≤
        ((unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k : ℝ) ∧
      ((unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k : ℝ) + buffer ≤
        (Green.boxSide (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer) k : ℝ) := by
  have h := BasisDefectLayout.boundary_margin S precision B hB D macroSpacing buffer hspacing ij k
  change (buffer : ℤ) + 1 ≤ (unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k ∧
    (unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k + ((buffer : ℤ) + 1) ≤ _ at h
  constructor
  · exact_mod_cast (show (buffer : ℤ) ≤ (unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k by omega)
  · exact_mod_cast (show (unionEmbedding (layout S precision B hB D macroSpacing buffer hspacing) ij).2 k + (buffer : ℤ) ≤
      (Green.boxSide (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer) k : ℤ) by omega)

/-- Finite PEC compression versus infinite compression, with every
geometric premise discharged by the actual encoder placement. -/
theorem finite_infinite_error
    [Nonempty (SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card)]
    (material : ScalarMaterial (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).nx
      (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).ny
      (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).nz)
    (m : Site → ℝ)
    (hcell : ∀ c : (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Cell,
      m (Target.latticeCell c) = (material.value c : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ e, |Target.latticeEdgeAverage m e| ≤ M)
    (A : EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge ≃L[ℂ]
      EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge)
    (H : Field ≃L[ℂ] Field) (σ : ℂ)
    (hA : (A : EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge →L[ℂ]
      EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge) =
        Green.pecMaxwellOperator material - σ • 1)
    (hH : (H : Field →L[ℂ] Field) = electricOperator (Target.latticeEdgeAverage m) M hM hm)
    (g τ J L μ : ℝ) (hg : 0 < g) (hμ : 0 ≤ μ)
    (hinv : ‖(H.symm : Field →L[ℂ] Field)‖ ≤ 1 / g)
    (hfinite : ‖(A.symm : EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge →L[ℂ]
      EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge)‖ ≤ L)
    (hnorm : ‖(H : Field →L[ℂ] Field)‖ ≤ J)
    (hτ : ‖σ‖ ≤ τ) (hσ : ‖σ‖ ≤ g / 4)
    (hsmall : 16 * (Real.exp (2 * μ) - 1) ≤ g / 4) :
    ‖realOperator (finite (layout S precision B hB D macroSpacing buffer hspacing)
        (A.symm : EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge →L[ℂ]
          EuclideanSpace ℂ (BasisDefectLayout.physicalBox S precision B D macroSpacing buffer).Edge)) -
      realOperator (infinite (layout S precision B hB D macroSpacing buffer hspacing) (H.symm : Field →L[ℂ] Field))‖ ≤
      2 * τ / g ^ 2 + (4 * J * L / g) * Real.exp (-μ * buffer) := by
  apply real_gram_error
  exact FiniteGram.finite_infinite_error _ material m hcell M hM hm A H σ hA hH g τ J L μ buffer
    hg hμ (by positivity) (union_margin S precision B hB D macroSpacing buffer hspacing)
    hinv hfinite hnorm hτ hσ hsmall

end Maxwell.Composition.SourceGram
