import Maxwell.Composition.PhysicalBright.Incidence
import Maxwell.Composition.PhysicalInteractions

/-! Exact identification of the physical nearest blocks with the routed
incidence matrix. Opposite edge displacements use the proved inverse symmetry. -/
noncomputable section
namespace Maxwell.Composition.PhysicalBright
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators InnerProduct

section Compression
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem interaction_bright_eq (q : EuclideanSpace ℝ κ)
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    (blockInjection q).adjoint.comp ((interactionOperator A).comp (blockInjection q)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (fun i j => inner ℝ q (A i j q)) := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  change (blockInjection q).adjoint (interactionOperator A (blockInjection q x)) i =
    ∑ j, inner ℝ q (A i j q) * x j
  rw [blockInjection_adjoint_coordinate, interaction_block_action]
  simp [blockCoordinate_injection, inner_sum, inner_smul_right, mul_comm]

end Compression

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _
attribute [local instance] Classical.propDecidable

def axial (k : Direction) : ℝ := inner ℝ P.mode
  (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
    ((d : ℤ) • P.basis.mulVec (unitSite k)) P.mode)

def near (i j : SourceDecoration.Vertex S precision) :=
  if SourceDecoration.Incident S precision i j then PhysicalInteractions.block P S precision d i j else 0

theorem incident_irrefl (i : SourceDecoration.Vertex S precision) :
    ¬ SourceDecoration.Incident S precision i i := by
  cases i <;> simp [SourceDecoration.Incident]

theorem scalar_block_symmetric (i j : SourceDecoration.Vertex S precision) :
    inner ℝ P.mode (PhysicalInteractions.block P S precision d i j P.mode) =
      inner ℝ P.mode (PhysicalInteractions.block P S precision d j i P.mode) := by
  unfold PhysicalInteractions.block
  have h : SourceDecoration.site S precision i - SourceDecoration.site S precision j =
      -(SourceDecoration.site S precision j - SourceDecoration.site S precision i) := by abel
  rw [h, Matrix.mulVec_neg, smul_neg, P.same_mode_even]

theorem tail_displacement (e : SourceIncidence.E S precision) :
    SourceDecoration.site S precision (.inl e.val.1) -
      SourceDecoration.site S precision (.inr e) = -unitSite (SourceIncidence.axis S precision e) := by
  rw [SourceDecoration.site, SourceDecoration.site, SourceIncidence.axis_spec S precision e]
  ext k
  simp only [DecoratedLattice.terminal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul]
  ring

theorem head_displacement (e : SourceIncidence.E S precision) :
    SourceDecoration.site S precision (.inl e.val.2) -
      SourceDecoration.site S precision (.inr e) = unitSite (SourceIncidence.axis S precision e) := by
  rw [SourceDecoration.site, SourceDecoration.site, SourceIncidence.axis_spec S precision e]
  ext k
  simp only [DecoratedLattice.terminal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem tail_coupling (e : SourceIncidence.E S precision) :
    inner ℝ P.mode (PhysicalInteractions.block P S precision d (.inl e.val.1) (.inr e) P.mode) =
      axial P d (SourceIncidence.axis S precision e) := by
  rw [PhysicalInteractions.block, tail_displacement S precision e, Matrix.mulVec_neg,
    smul_neg, P.same_mode_even]
  rfl

theorem head_coupling (e : SourceIncidence.E S precision) :
    inner ℝ P.mode (PhysicalInteractions.block P S precision d (.inl e.val.2) (.inr e) P.mode) =
      axial P d (SourceIncidence.axis S precision e) := by
  rw [PhysicalInteractions.block, head_displacement S precision e]
  rfl

theorem scalar_near_left_right (v : SourceIncidence.V S precision)
    (e : SourceIncidence.E S precision) :
    inner ℝ P.mode (near P S precision d (.inl v) (.inr e) P.mode) =
      (SourceIncidence.graph S precision).coupling
        (fun e => axial P d (SourceIncidence.axis S precision e)) v e := by
  by_cases ht : v = e.val.1
  · subst v
    simp only [near, SourceDecoration.Incident, true_or, ↓reduceIte, SignedIncidence.coupling,
      SignedIncidence.incidence, SourceIncidence.graph, one_mul]
    exact tail_coupling P S precision d e
  · by_cases hh : v = e.val.2
    · subst v
      simp only [near, SourceDecoration.Incident, or_true, ↓reduceIte, SignedIncidence.coupling,
        SignedIncidence.incidence, SourceIncidence.graph, ht, one_mul]
      exact head_coupling P S precision d e
    · simp [near, SourceDecoration.Incident, ht, hh, SignedIncidence.coupling,
        SignedIncidence.incidence, SourceIncidence.graph]

theorem scalar_near_eq_incidence :
    (fun i j => inner ℝ P.mode (near P S precision d i j P.mode)) =
      incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => axial P d (SourceIncidence.axis S precision e)) := by
  funext i j
  cases i with
  | inl v =>
    cases j with
    | inl w => simp [near, SourceDecoration.Incident, incidenceMatrix]
    | inr e => exact scalar_near_left_right P S precision d v e
  | inr e =>
    cases j with
    | inl v =>
      have h : inner ℝ P.mode (near P S precision d (.inr e) (.inl v) P.mode) =
          inner ℝ P.mode (near P S precision d (.inl v) (.inr e) P.mode) := by
        by_cases hi : v = e.val.1 ∨ v = e.val.2
        · simp only [near, SourceDecoration.Incident, hi, ↓reduceIte]
          exact scalar_block_symmetric P S precision d _ _
        · simp [near, SourceDecoration.Incident, hi]
      rw [h]
      exact scalar_near_left_right P S precision d v e
    | inr f => simp [near, SourceDecoration.Incident, incidenceMatrix]

/-- The actual projected nearest Green blocks have exactly the physical
axis couplings on the actual routed incidence graph. -/
theorem near_bright_eq :
    (blockInjection P.mode).adjoint.comp
      ((interactionOperator (near P S precision d)).comp (blockInjection P.mode)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => axial P d (SourceIncidence.axis S precision e))) := by
  rw [interaction_bright_eq, scalar_near_eq_incidence]

theorem offdiag_near_far :
    interactionOperator (PhysicalInteractions.offdiag P S precision d) =
      interactionOperator (near P S precision d) +
        interactionOperator (PhysicalInteractions.far P S precision d) := by
  have h : PhysicalInteractions.offdiag P S precision d =
      fun i j => near P S precision d i j + PhysicalInteractions.far P S precision d i j := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp [PhysicalInteractions.offdiag, PhysicalInteractions.far, near, incident_irrefl]
    · by_cases hi : SourceDecoration.Incident S precision i j <;>
        simp [PhysicalInteractions.offdiag, PhysicalInteractions.far, near, hij, hi]
  rw [h]
  ext x ⟨i, k⟩
  change (∑ j, (near P S precision d i j + PhysicalInteractions.far P S precision d i j)
    (blockCoordinate x j)) k =
    (∑ j, near P S precision d i j (blockCoordinate x j)) k +
      (∑ j, PhysicalInteractions.far P S precision d i j (blockCoordinate x j)) k
  simp [Finset.sum_add_distrib]

/-- Independent axial rounding errors induce exactly the routed incidence
error, whose complete operator norm is at most three times the tolerance. -/
theorem near_calibration_bound (β : Direction → ℚ) (R : ℝ) (hR : 0 ≤ R)
    (hβ : ∀ k, |(β k : ℝ) + axial P d k| ≤ R) :
    ‖-((blockInjection P.mode).adjoint.comp
      ((interactionOperator (near P S precision d)).comp (blockInjection P.mode))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ)))‖ ≤ 3 * R := by
  rw [near_bright_eq]
  have heq :
      -Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => axial P d (SourceIncidence.axis S precision e))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ))) =
      -Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
        (fun e => axial P d (SourceIncidence.axis S precision e) +
          (β (SourceIncidence.axis S precision e) : ℝ))) := by
    rw [incidenceMatrix_add, map_add]
    abel
  rw [heq, _root_.norm_neg]
  apply source_incidence_norm_le S precision _ R hR
  intro e
  simpa only [add_comm] using hβ (SourceIncidence.axis S precision e)

end Maxwell.Composition.PhysicalBright
