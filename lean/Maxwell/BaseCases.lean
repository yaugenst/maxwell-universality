import Maxwell.Target

/-!
# Exact finite base cases

For a nonsingular sparse source with at most one stored nonzero, there is
at most one variable. The exact-solve constructor performs the corresponding
rational scalar division and stores that answer in an empty-sampling decoder. The
emitted physical system is the actual scalar-material-one, `1 × 2 × 2` PEC
box, whose sole Maxwell entry is `255/64`. No recovery statement is assumed.

The separate `zeroInstance` constructor uses a zero offset and requires no
division. It satisfies every requested accuracy in the source contract:
one stored nonzero forces the requested relative tolerance to equal one;
zero stored nonzeros forces the source to vanish.
-/

namespace Maxwell.BaseCases

open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem index_eq {n : ℕ} (hn : n ≤ 1) (i j : Fin n) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The only arithmetic operation needed for an inhabited base source. -/
def solution (S : Source.SparseSystem) : Fin S.n → ℚ :=
  fun i => S.source i / S.matrix.toMatrix i i

theorem diagonal_ne_zero (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) (i : Fin S.n) :
    S.matrix.toMatrix i i ≠ 0 := by
  obtain ⟨j, hj⟩ := Source.row_has_nonzero S hunit i
  have hij := index_eq ((Source.dimension_le_nnz S hunit).trans hm) j i
  simpa only [hij] using hj

/-- Exact rational equality, including the vacuous empty-dimensional case. -/
theorem solution_mulVec (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) :
    S.matrix.toMatrix.mulVec (solution S) = S.source := by
  classical
  funext i
  change ∑ j : Fin S.n, S.matrix.toMatrix i j * solution S j = S.source i
  rw [Finset.sum_eq_single i]
  · dsimp [solution]
    field_simp [diagonal_ne_zero S hunit hm i]
  · intro j _ hji
    exact (hji (index_eq ((Source.dimension_le_nnz S hunit).trans hm) j i)).elim
  · simp

/-- The exact scalar solve satisfies the actual Euclidean source equation. -/
theorem solution_exact (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) :
    Source.operator S (Source.rationalVector (solution S)) = Source.rhs S := by
  ext i
  change ∑ j : Fin S.n, (S.matrix.toMatrix i j : ℝ) * (solution S j : ℝ) =
    (S.source i : ℝ)
  have h := congrFun (solution_mulVec S hunit hm) i
  exact_mod_cast h

abbrev box : Target.Box := ⟨1, 2, 2⟩

instance : Subsingleton box.Edge := ⟨Fintype.card_le_one_iff.mp (by
  norm_num [box, Target.Box.Edge, retainedEdge_card])⟩

instance : Nonempty box.Edge :=
  ⟨Sum.inl (⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩)⟩

-- Cache the finite-index dictionaries: expanding all nested sum/product
-- equality instances inside a matrix norm exceeds Lean's default size limit.
local instance : Fintype box.Edge := inferInstance
local instance : DecidableEq box.Edge := inferInstance

def material : ScalarMaterial box.nx box.ny box.nz where
  value _ := 1
  bounds _ := by norm_num

/-- A genuine weighted decoder with no access to the physical output. -/
def decoder (S : Source.SparseSystem) : Target.WeightedDecoder box.Edge S.n where
  sampleCount := 0
  coordinate := Fin.elim0
  format := ⟨0, 0⟩
  support _ := ∅
  weight _ := Fin.elim0
  offset := solution S

/-- This constructor emits physical data for every finite source; correctness
below is asserted only under nonsingularity and the explicit size bound. -/
abbrev physicalInstance (S : Source.SparseSystem) : Target.Instance S.n where
  box := box
  material := material
  source _ := 0
  tolerance := 1
  tolerance_pos := by norm_num
  decoder := decoder S

@[simp] theorem instance_dimension (S : Source.SparseSystem) :
    (physicalInstance S).dimension = 1 := by
  norm_num [physicalInstance, Target.Instance.dimension, box, Target.Box.Edge,
    retainedEdge_card]

@[simp] theorem instance_cellCount (S : Source.SparseSystem) :
    (physicalInstance S).cellCount = 4 := by
  norm_num [physicalInstance, Target.Instance.cellCount, box, Target.Box.Cell, Cell]

@[simp] theorem decoder_sampleCount (S : Source.SparseSystem) :
    (physicalInstance S).decoder.sampleCount = 0 := rfl

@[simp] theorem decoder_decode (S : Source.SparseSystem)
    (w : (physicalInstance S).decoder.Messages) :
    (physicalInstance S).decoder.decode w = solution S := by
  funext i
  simp [physicalInstance, decoder, Target.WeightedDecoder.decode]

theorem decoder_fits (S : Source.SparseSystem) (y : (physicalInstance S).box.Edge → ℝ) :
    (physicalInstance S).decoder.Fits y := by
  intro j
  exact Fin.elim0 j

theorem decoder_accurate (S : Source.SparseSystem)
    (w : (physicalInstance S).decoder.Messages) (y : (physicalInstance S).box.Edge → ℝ) :
    (physicalInstance S).decoder.Accurate w y := by
  intro j
  exact Fin.elim0 j

def messages (S : Source.SparseSystem) : (physicalInstance S).decoder.Messages :=
  Fin.elim0

/-- Every finite message, hence every possible solver vector and readout,
returns the exact source solution. No physical-residual hypothesis is needed. -/
theorem decoder_exact (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (w : (physicalInstance S).decoder.Messages) :
    Source.operator S (Source.rationalVector ((physicalInstance S).decoder.decode w)) =
      Source.rhs S := by
  rw [decoder_decode]
  exact solution_exact S hunit hm

theorem recovery (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (eta : ℝ) (heta : 0 ≤ eta) (w : (physicalInstance S).decoder.Messages) :
    Source.ResidualTarget S eta ((physicalInstance S).decoder.decode w) := by
  unfold Source.ResidualTarget
  rw [decoder_exact S hunit hm w, sub_self, norm_zero]
  exact mul_nonneg heta (norm_nonneg _)

/-- Every complex physical vector admits an actual finite readout returning
an exact rational source solution, without requiring a preferred representative
or even assuming that its physical residual is acceptable. -/
theorem every_complex_vector_recovery (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (eta : ℝ) (heta : 0 ≤ eta)
    (y : EuclideanSpace ℂ (physicalInstance S).box.Edge) :
    ∃ w : (physicalInstance S).decoder.Messages,
      (physicalInstance S).decoder.Accurate w (fun e => (y e).re) ∧
      Source.operator S (Source.rationalVector ((physicalInstance S).decoder.decode w)) =
        Source.rhs S ∧
      Source.ResidualTarget S eta ((physicalInstance S).decoder.decode w) :=
  ⟨messages S, decoder_accurate S (messages S) _,
    decoder_exact S hunit hm (messages S), recovery S hunit hm eta heta (messages S)⟩

/-- The emitted physical problem itself has an exact admissible solution. -/
theorem zero_admissible (S : Source.SparseSystem) :
    (physicalInstance S).Admissible 0 := by
  have hf : (physicalInstance S).complexSource = 0 := by
    ext e
    simp [Target.Instance.complexSource, physicalInstance]
  simp [Target.Instance.Admissible, hf]

theorem instance_realMatrix (S : Source.SparseSystem) :
    (physicalInstance S).realMatrix =
      (255 / 64 : ℝ) • (1 : Matrix box.Edge box.Edge ℝ) := by
  ext e f
  have hef : e = f := @Subsingleton.elim box.Edge inferInstance e f
  subst f
  have h := Target.one_edge_operator e
  change ((Target.operator box (fun _ => 1) e e : ℚ) : ℝ) = _
  rw [h]
  norm_num [Matrix.smul_apply]

theorem instance_inverse (S : Source.SparseSystem) :
    ((physicalInstance S).realMatrix : Matrix box.Edge box.Edge ℝ)⁻¹ =
      (64 / 255 : ℝ) • (1 : Matrix box.Edge box.Edge ℝ) := by
  apply Matrix.inv_eq_left_inv
  rw [instance_realMatrix]
  norm_num [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem instance_isUnit (S : Source.SparseSystem) :
    IsUnit ((physicalInstance S).realMatrix : Matrix box.Edge box.Edge ℝ) := by
  refine ⟨⟨((physicalInstance S).realMatrix : Matrix box.Edge box.Edge ℝ),
    (64 / 255 : ℝ) • (1 : Matrix box.Edge box.Edge ℝ), ?_, ?_⟩, rfl⟩ <;>
    rw [instance_realMatrix] <;>
    norm_num [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Conditioning concerns the entire actual Maxwell matrix, not a reduced
block or an assumed matrix supplied by a caller. -/
theorem instance_condition (S : Source.SparseSystem) :
    condition₂ (physicalInstance S).realMatrix = 1 := by
  change ‖((physicalInstance S).realMatrix : Matrix box.Edge box.Edge ℝ)‖ *
    ‖((physicalInstance S).realMatrix : Matrix box.Edge box.Edge ℝ)⁻¹‖ = 1
  rw [instance_inverse S, instance_realMatrix S]
  norm_num [norm_smul]

/-- The base-case bit program can emit this decoder without scalar division. -/
def zeroDecoder (S : Source.SparseSystem) : Target.WeightedDecoder box.Edge S.n where
  sampleCount := 0
  coordinate := Fin.elim0
  format := ⟨0, 0⟩
  support _ := ∅
  weight _ := Fin.elim0
  offset := 0

/-- The same genuine physical system, with an identically zero readout. -/
abbrev zeroInstance (S : Source.SparseSystem) : Target.Instance S.n where
  box := box
  material := material
  source _ := 0
  tolerance := 1
  tolerance_pos := by norm_num
  decoder := zeroDecoder S

@[simp] theorem zero_instance_dimension (S : Source.SparseSystem) :
    (zeroInstance S).dimension = 1 := instance_dimension S

@[simp] theorem zero_instance_cellCount (S : Source.SparseSystem) :
    (zeroInstance S).cellCount = 4 := instance_cellCount S

@[simp] theorem zero_decoder_sampleCount (S : Source.SparseSystem) :
    (zeroInstance S).decoder.sampleCount = 0 := rfl

@[simp] theorem zero_decoder_decode (S : Source.SparseSystem)
    (w : (zeroInstance S).decoder.Messages) :
    (zeroInstance S).decoder.decode w = 0 := by
  funext i
  simp [zeroInstance, zeroDecoder, Target.WeightedDecoder.decode]

theorem zero_decoder_fits (S : Source.SparseSystem)
    (y : (zeroInstance S).box.Edge → ℝ) : (zeroInstance S).decoder.Fits y := by
  intro j
  exact Fin.elim0 j

theorem zero_decoder_accurate (S : Source.SparseSystem)
    (w : (zeroInstance S).decoder.Messages) (y : (zeroInstance S).box.Edge → ℝ) :
    (zeroInstance S).decoder.Accurate w y := by
  intro j
  exact Fin.elim0 j

def zero_messages (S : Source.SparseSystem) : (zeroInstance S).decoder.Messages :=
  Fin.elim0

/-- Every finite message meets every requested source tolerance in the base
cases. No physical-residual hypothesis or scalar division is needed. -/
theorem zero_recovery_requested (p : Source.Parameters) (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta)
    (w : (zeroInstance S).decoder.Messages) :
    Source.ResidualTarget S eta ((zeroInstance S).decoder.decode w) := by
  rw [zero_decoder_decode]
  by_cases hzero : S.nnz = 0
  · exact Source.zero_source_residual S eta (Source.source_zero_of_nnz_zero S hunit hzero)
  · have hone : S.nnz = 1 := by omega
    have heta1 : eta = 1 := le_antisymm heta.2 (by simpa [hone] using heta.1)
    have hx : Source.rationalVector (0 : Fin S.n → ℚ) = 0 := by
      ext i
      simp [Source.rationalVector]
    simp [Source.ResidualTarget, hx, heta1]

/-- Every complex physical vector admits the actual empty finite readout;
recovery holds for every message, independently of that vector. -/
theorem zero_every_complex_vector_recovery (p : Source.Parameters)
    (S : Source.SparseSystem) (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta)
    (y : EuclideanSpace ℂ (zeroInstance S).box.Edge) :
    ∃ w : (zeroInstance S).decoder.Messages,
      (zeroInstance S).decoder.Accurate w (fun e => (y e).re) ∧
      Source.ResidualTarget S eta ((zeroInstance S).decoder.decode w) :=
  ⟨zero_messages S, zero_decoder_accurate S (zero_messages S) _,
    zero_recovery_requested p S hunit hm eta heta (zero_messages S)⟩

theorem zero_instance_admissible (S : Source.SparseSystem) :
    (zeroInstance S).Admissible 0 := zero_admissible S

theorem zero_instance_realMatrix (S : Source.SparseSystem) :
    (zeroInstance S).realMatrix =
      (255 / 64 : ℝ) • (1 : Matrix box.Edge box.Edge ℝ) := instance_realMatrix S

theorem zero_instance_isUnit (S : Source.SparseSystem) :
    IsUnit ((zeroInstance S).realMatrix : Matrix box.Edge box.Edge ℝ) := instance_isUnit S

theorem zero_instance_condition (S : Source.SparseSystem) :
    condition₂ (zeroInstance S).realMatrix = 1 := instance_condition S

end Maxwell.BaseCases
