import Maxwell.Continuum.FiniteAuxiliaryNearest
import Maxwell.Continuum.FiniteAuxiliaryCoupling
import Maxwell.Continuum.FiniteAuxiliaryBrightDiagonal
import Maxwell.Composition.PhysicalBright.Incidence
import Maxwell.Composition.ComplexInverse

/-! The actual continuum nearest blocks compress to the calibrated
degree-three incidence matrix, in both physical orientations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] realMode

theorem nearBlocks_adjoint {ι : Type*} [Fintype ι] {L : ℕ} {z : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (position : ι → Bloch.Alias) (i j : ι) :
    (nearBlocks D d position i j).adjoint = nearBlocks D d position j i := by
  have hn : latticeOneNorm (position j-position i) = latticeOneNorm (position i-position j) := by
    rw [show position j-position i = -(position i-position j) by abel, latticeOneNorm_neg]
  by_cases he : latticeOneNorm (position i-position j) = 1
  · simp only [nearBlocks, hn, he, ite_true, physicalWellBlock_adjoint, neg_sub]
  · simp only [nearBlocks, hn, he, ite_false, map_zero]

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem source_near_left_right {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ)
    (v : SourceIncidence.V S precision) (e : SourceIncidence.E S precision) :
    inner ℂ (realMode D (inverse_length_le_1024 hL))
      (nearBlocks D d (SourceDecoration.site S precision) (.inl v) (.inr e)
        (realMode D (inverse_length_le_1024 hL))) =
      (((SourceIncidence.graph S precision).coupling
        (fun e => usefulCoupling hL D d (SourceIncidence.axis S precision e)) v e : ℝ) : ℂ) := by
  by_cases ht : v = e.val.1
  · subst v
    have hi := (source_nearest_iff S precision (.inl e.val.1) (.inr e)).mpr (Or.inl rfl)
    rw [nearBlocks, ite_eq_left hi, source_tail_displacement,
      opposite_usefulCoupling hL D d (SourceIncidence.axis S precision e)]
    simp only [SignedIncidence.coupling, SignedIncidence.incidence, SourceIncidence.graph,
      ite_true, one_mul]
  · by_cases hh : v = e.val.2
    · subst v
      have hi := (source_nearest_iff S precision (.inl e.val.2) (.inr e)).mpr (Or.inr rfl)
      rw [nearBlocks, ite_eq_left hi, source_head_displacement,
        usefulCoupling_real hL D d (SourceIncidence.axis S precision e)]
      simp only [SignedIncidence.coupling, SignedIncidence.incidence, SourceIncidence.graph,
        ht, ite_false, ite_true, one_mul]
    · have hi : latticeOneNorm (SourceDecoration.site S precision (.inl v)-
          SourceDecoration.site S precision (.inr e)) ≠ 1 := by
        intro he
        exact (not_or.mpr ⟨ht, hh⟩)
          ((source_nearest_iff S precision (.inl v) (.inr e)).mp he)
      simp [nearBlocks, hi, SignedIncidence.coupling, SignedIncidence.incidence,
        SourceIncidence.graph, ht, hh]

theorem source_near_matrix {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) :
    (fun i j => inner ℂ (realMode D (inverse_length_le_1024 hL))
      (nearBlocks D d (SourceDecoration.site S precision) i j
        (realMode D (inverse_length_le_1024 hL)))) =
      (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => usefulCoupling hL D d (SourceIncidence.axis S precision e))).map Complex.ofReal := by
  funext i j
  cases i with
  | inl v =>
    cases j with
    | inl w => simp [nearBlocks, source_nearest_iff, SourceDecoration.Incident, PhysicalBright.incidenceMatrix]
    | inr e => exact source_near_left_right S precision hL D d v e
  | inr e =>
    cases j with
    | inl v =>
      rw [← nearBlocks_adjoint D d (SourceDecoration.site S precision) (.inl v) (.inr e),
        ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
        source_near_left_right S precision hL D d v e]
      simp [PhysicalBright.incidenceMatrix]
    | inr f => simp [nearBlocks, source_nearest_iff, SourceDecoration.Incident, PhysicalBright.incidenceMatrix]

theorem source_near_bright {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) :
    (brightCoefficient (realMode D (inverse_length_le_1024 hL))).comp
      ((blockOperator (nearBlocks D d (SourceDecoration.site S precision))).comp
        (bright (realMode D (inverse_length_le_1024 hL)))) =
      ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => usefulCoupling hL D d (SourceIncidence.axis S precision e))) := by
  rw [block_bright_matrix, source_near_matrix]
  rfl

theorem source_near_calibration_norm {L : ℕ} {z R : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (β : Fin 3 → ℝ) (hR : 0 ≤ R)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ R) :
    ‖-((brightCoefficient (realMode D (inverse_length_le_1024 hL))).comp
      ((blockOperator (nearBlocks D d (SourceDecoration.site S precision))).comp
        (bright (realMode D (inverse_length_le_1024 hL)))))-
      ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => β (SourceIncidence.axis S precision e)))‖ ≤ 3*R := by
  rw [source_near_bright S precision hL D d]
  have he : -ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
      (fun e => usefulCoupling hL D d (SourceIncidence.axis S precision e)))-
      ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => β (SourceIncidence.axis S precision e))) =
      -ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => usefulCoupling hL D d (SourceIncidence.axis S precision e)+β (SourceIncidence.axis S precision e))) := by
    rw [PhysicalBright.incidenceMatrix_add, complexOperator_add]
    abel
  rw [he, _root_.norm_neg, ComplexInverse.complexOperator_norm]
  apply PhysicalBright.source_incidence_norm_le S precision _ R hR
  intro e
  simpa only [add_comm] using hβ (SourceIncidence.axis S precision e)

#print axioms source_near_bright
#print axioms source_near_calibration_norm

end Maxwell.Continuum.FiniteAuxiliary
