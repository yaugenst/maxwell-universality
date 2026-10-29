import Maxwell.Composition.PositiveRational
import Maxwell.Logical.RationalScatter

/-! Linear sparse scatter of the actual rational positive-graph diagonal.
Every emitted H entry produces exactly three accumulator updates. -/

namespace Maxwell.Composition.PositiveScatter
open Maxwell.Logical
open RationalScatter

/-- Three literal updates for one nonzero circuit coefficient. -/
def term {d count : ℕ} (pair : Fin d × Fin d) (weight : ℚ) (k : Fin count) :
    List (Update (d + d + count)) :=
  [⟨finSumFinEquiv (.inl (finSumFinEquiv (.inl pair.1))), -weight⟩,
   ⟨finSumFinEquiv (.inl (finSumFinEquiv (.inr pair.2))), -weight⟩,
   ⟨finSumFinEquiv (.inr k), -weight⁻¹⟩]

@[simp] theorem term_length {d count : ℕ} (pair : Fin d × Fin d) (weight : ℚ)
    (k : Fin count) : (term pair weight k).length = 3 := rfl

theorem term_old {d count : ℕ} (pair : Fin d × Fin d) (weight : ℚ)
    (k : Fin count) (v : Fin d ⊕ Fin d) :
    sumAt (term pair weight k) (finSumFinEquiv (.inl (finSumFinEquiv v))) =
      -(match v with
        | .inl i => (if i = pair.1 then 1 else 0)
        | .inr j => (if j = pair.2 then 1 else 0)) * weight := by
  cases v <;>
    simp only [sumAt, term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, ↓reduceIte, add_zero, zero_add]
  all_goals split_ifs <;> simp_all

theorem term_mediator {d count : ℕ} (pair : Fin d × Fin d) (weight : ℚ)
    (k j : Fin count) :
    sumAt (term pair weight k) (finSumFinEquiv (.inr j)) =
      if k = j then -weight⁻¹ else 0 := by
  simp only [sumAt, term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Equiv.apply_eq_iff_eq, Sum.inl_ne_inr, Sum.inr.injEq, ↓reduceIte, zero_add, add_zero]

/-- Cache both source arrays before entering the nonzero loop. -/
def updates (S : Source.SparseSystem) (precision : ℕ) :
    List (Update ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :=
  let pairs := SourceCached.pair S precision
  let values := SourceCached.entries S precision
  (List.finRange (sourceSquareEntries S precision).length).flatMap
    (fun k => term (pairs k) (values.get k).value k)

theorem updates_length (S : Source.SparseSystem) (precision : ℕ) :
    (updates S precision).length = 3 * (sourceSquareEntries S precision).length := by
  simp [updates, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn, mul_comm]

theorem sumAt_updates (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    sumAt (updates S precision) i =
      ∑ k, sumAt (term (SourceEnumeration.pair S precision k)
        (SourceEnumeration.entry S precision k).value k) i := by
  rw [updates, sumAt_flatMap]
  simp [List.finRange, List.map_ofFn, List.sum_ofFn]

theorem updates_correct (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    sumAt (updates S precision) i = PositiveRational.diagonal S precision i := by
  rw [sumAt_updates]
  obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective i
  cases v with
  | inl v =>
      obtain ⟨w, rfl⟩ := finSumFinEquiv.surjective v
      simp only [term_old, PositiveRational.diagonal, Equiv.symm_apply_apply,
        PositiveRational.endpointDiagonal]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [neg_mul]
      congr 1
      cases w <;> rfl
  | inr k =>
      simp only [term_mediator, PositiveRational.diagonal, Equiv.symm_apply_apply]
      simp

/-- The actual computed coefficient array: one zero allocation and 3K updates. -/
def diagonal (S : Source.SparseSystem) (precision : ℕ) :
    Vector ℚ ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length) :=
  materialize (updates S precision)

@[simp] theorem diagonal_get (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    (diagonal S precision).get i = PositiveRational.diagonal S precision i := by
  rw [diagonal, materialize_get, updates_correct]

theorem diagonal_cast (S : Source.SparseSystem) (precision : ℕ)
    (v : SourcePositive.Vertex S precision) :
    ((diagonal S precision).get (SourceEnumeration.vertexEquiv S precision v) : ℝ) =
      PositiveEdges.diagonal (SourcePositive.sourceH S precision) v := by
  rw [diagonal_get, PositiveRational.diagonal_cast]


theorem diagonal_abs_le_three (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) : |(diagonal S precision).get i| ≤ 3 := by
  obtain ⟨v, rfl⟩ := (SourceEnumeration.vertexEquiv S precision).surjective i
  have h := PositiveEdges.diagonal_abs_le_three (SourcePositive.sourceH S precision)
    (SourcePositive.alphabet S precision) (SourcePositive.rowSupport_le_three S precision)
    (SourcePositive.columnSupport_le_three S precision) v
  rw [← diagonal_cast] at h
  exact_mod_cast h

theorem diagonal_half_integer (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    ∃ a : ℤ, (diagonal S precision).get i = (a : ℚ) / 2 := by
  obtain ⟨v, rfl⟩ := (SourceEnumeration.vertexEquiv S precision).surjective i
  have hex : ∃ a : ℤ, PositiveEdges.diagonal (SourcePositive.sourceH S precision) v = (a : ℝ) / 2 := by
    cases v with
    | inl v =>
        exact PositiveEdges.endpoint_half_integer (SourcePositive.sourceH S precision)
          (SourcePositive.alphabet S precision) v
    | inr e =>
        have h := PositiveEdges.mediator_alphabet (SourcePositive.sourceH S precision)
          (SourcePositive.alphabet S precision) e
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h | h
        · exact ⟨-4, by change -(PositiveEdges.weight _ e)⁻¹ = _; rw [h]; norm_num⟩
        · exact ⟨-2, by change -(PositiveEdges.weight _ e)⁻¹ = _; rw [h]; norm_num⟩
        · exact ⟨2, by change -(PositiveEdges.weight _ e)⁻¹ = _; rw [h]; norm_num⟩
        · exact ⟨4, by change -(PositiveEdges.weight _ e)⁻¹ = _; rw [h]; norm_num⟩
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  rw [← diagonal_cast] at ha
  exact_mod_cast ha

/-- The fixed signed half-integer code is extracted from the computed array. -/
def numerator (S : Source.SparseSystem) (precision : ℕ) :
    Vector ℤ ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length) :=
  (diagonal S precision).map (fun q => (2 * q).num)

theorem numerator_exact (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) :
    ((numerator S precision).get i : ℚ) / 2 = (diagonal S precision).get i := by
  obtain ⟨a, ha⟩ := diagonal_half_integer S precision i
  have hg : (numerator S precision).get i = (2 * (diagonal S precision).get i).num := by
    simp [numerator, Vector.get, Fin.cast]
  rw [hg, ha, show (2 : ℚ) * ((a : ℚ) / 2) = (a : ℚ) by ring, Rat.num_intCast]

theorem numerator_abs_le_six (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) : |(numerator S precision).get i| ≤ 6 := by
  have h := diagonal_abs_le_three S precision i
  rw [← numerator_exact] at h
  have hr : |((numerator S precision).get i : ℚ)| ≤ 6 := by
    rw [abs_div] at h
    norm_num at h
    linarith
  exact_mod_cast hr

end Maxwell.Composition.PositiveScatter
