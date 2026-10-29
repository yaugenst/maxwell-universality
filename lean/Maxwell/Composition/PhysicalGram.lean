import Maxwell.Composition.PhysicalBuffer
import Maxwell.Composition.PhysicalInteractions
import Maxwell.Composition.CoreGram

/-! The literal selected finite PEC background, compressed on the whole
decorated defect union, approximates the actual infinite Green block matrix.
Every geometry, material, spectral-event, and buffer premise is discharged. -/
noncomputable section
namespace Maxwell.Composition.PhysicalGram
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Composition.FiniteGram

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

abbrev box := DecoratedDefectLayout.physicalBox S precision P.basis P.defect d
  (P.chosenBuffer S precision d ζ hζ hζ1)

abbrev layout (hd : P.spacing.minimumDistance ≤ d) :=
  DecoratedDefectLayout.layout S precision P.basis P.basis_injective P.defect d
    (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd)

abbrev width := P.constants.detuningWidth ζ hζ

abbrev bad (J : ℕ) := PhysicalBackground.bad P (box P S precision d ζ hζ hζ1)
  S.nnz J (width P ζ hζ)

abbrev background (hm : 0 < S.nnz) (J : ℕ) (j : Fin J)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) :=
  PhysicalBackground.complexEquiv P (box P S precision d ζ hζ hζ1) S.nnz J
    (width P ζ hζ) hm (P.constants.detuningWidth_pos ζ hζ) j hj

def finiteGram (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz) (J : ℕ) (j : Fin J)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) :=
  realOperator (finite (layout P S precision d ζ hζ hζ1 hd)
    ((background P S precision d ζ hζ hζ1 hm J j hj).symm :
      EuclideanSpace ℂ (box P S precision d ζ hζ hζ1).Edge →L[ℂ]
        EuclideanSpace ℂ (box P S precision d ζ hζ hζ1).Edge))

def infiniteGram := interactionOperator (PhysicalInteractions.block P S precision d)

theorem infiniteGram_eq (hd : P.spacing.minimumDistance ≤ d) :
    realOperator (infinite (layout P S precision d ζ hζ hζ1 hd)
      (P.bulk.symm : Field →L[ℂ] Field)) = infiniteGram P S precision d := by
  have h := DecoratedGram.infinite_blocks S precision P.basis P.basis_injective P.defect d
    (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd)
    P.background.edgeMaterial 25 (by norm_num) P.background.edge_bound 0
  have hzero : electricOperator (periodicCoefficient P.background.edgeMaterial) 25
      (by norm_num) P.background.edge_bound - (0 : ℂ) • 1 = P.background.operator := by
    ext x e
    change (P.background.operator x) e - (0 : ℂ) * x e = (P.background.operator x) e
    ring
  rw [hzero] at h
  rw [← PeriodicScalarBackground.bulk_inverse_eq P] at h
  exact h

private theorem local_nonempty : Nonempty (Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card) := by
  by_contra hn
  have : IsEmpty (Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card) := not_nonempty_iff.mp hn
  have hz : P.mode = 0 := Subsingleton.elim _ _
  have hu := P.mode_unit
  rw [hz, norm_zero] at hu
  norm_num at hu

private theorem sites_nonempty (hm : 0 < S.nnz) : Nonempty (SourceDecoration.Vertex S precision) := by
  obtain ⟨ij, _⟩ := Finset.card_pos.mp hm
  exact ⟨Sum.inl (SourceRouting.inputCoordinate S precision ij.1)⟩

/-- One event controls the complete compression, not a union bound over
individual Green entries or an output-dependent event. -/
theorem finiteGram_error (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz)
    (J : ℕ) (j : Fin J) (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) :
    ‖finiteGram P S precision d ζ hζ hζ1 hd hm J j hj - infiniteGram P S precision d‖ ≤
      (ζ : ℝ)^2 := by
  have := local_nonempty P
  have := sites_nonempty S precision hm
  let τ := width P ζ hζ
  let σ := Probability.rationalMidpoint τ J j.val
  have hτ := P.constants.detuningWidth_pos ζ hζ
  have hσ := Probability.rationalMidpoint_mem τ J j hτ
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ.1
  have hnorm : ‖(σ : ℂ)‖ = (σ : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσR]
  have hsmallσ : ‖(σ : ℂ)‖ ≤ (P.bulkGap : ℝ)/4 := by
    rw [hnorm]
    exact_mod_cast hσ.2.le.trans (P.constants.detuningWidth_bounds ζ hζ).2.1
  have havg : ∀ e, |Target.latticeEdgeAverage P.background.scalar e| ≤ (25 : ℝ) := by
    intro e
    rw [P.background.lattice_average]
    exact P.background.edge_bound e
  have hbound := DecoratedGram.finite_infinite_error S precision P.basis P.basis_injective
    P.defect d (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd)
    (PhysicalBackground.material P (box P S precision d ζ hζ hζ1)) P.background.scalar
    (fun _ => rfl) 25 (by norm_num) havg
    (background P S precision d ζ hζ hζ1 hm J j hj) P.bulk (σ : ℂ)
    (PhysicalBackground.complex_operator P _ S.nnz J τ hm hτ j hj)
    (P.bulk_operator.trans (P.background.operator_lattice 25 (by norm_num) havg))
    (P.bulkGap : ℝ) (τ : ℝ) (P.rowBound : ℝ)
    (P.constants.backgroundInverseBudget ζ hζ S.nnz
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge) : ℝ)
    (P.combesExponent : ℝ) (by exact_mod_cast P.bulkGap_pos)
    (by exact_mod_cast P.combesExponent_pos.le) P.bulk_inverse_bound
    (by rw [P.constants.backgroundInverseBudget_cast]; exact PhysicalBackground.complex_inverse_bound P _ S.nnz J τ hm hτ j hj)
    P.bulk_norm_bound (by rw [hnorm]; exact_mod_cast hσ.2.le) hsmallσ P.combesExponent_small
  rw [infiniteGram_eq P S precision d ζ hζ hζ1 hd] at hbound
  exact hbound.trans (P.chosenBuffer_error S precision d ζ hζ hζ1)

end Maxwell.Composition.PhysicalGram
