import Maxwell.Composition.SourcePositive
import Maxwell.Logical.RationalSupport

/-! A concrete enumeration of the nonzero circuit entries, obtained directly
from the emitted sparse list. This is the index set of positive mediators. -/

namespace Maxwell.Composition.SourceEnumeration
open Maxwell.Logical

def entry (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) : RationalCode.Entry :=
  (sourceSquareEntries S precision).get i

theorem entry_mem (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    entry S precision i ∈ sourceSquareEntries S precision := List.get_mem _ _

def pair (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    Fin (sourceCircuit S precision).size × Fin (sourceCircuit S precision).size :=
  let e := entry S precision i
  let hb := (sourceCircuit_rational S precision).code.squareEntries_bounded
    (sourceOutput S precision) e (entry_mem S precision i)
  (⟨e.row, hb.1⟩, ⟨e.column, hb.2⟩)

theorem sourceH_pair (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    SourcePositive.sourceH S precision (pair S precision i).1 (pair S precision i).2 =
      ((entry S precision i).value : ℝ) := by
  rw [show SourcePositive.sourceH S precision = (sourceSquareMap S precision).toMatrix' from rfl,
    ← sourceSquareMatrixQ_cast, ← sourceSquareEntries_matrix]
  change (RationalCode.entrySum (sourceSquareEntries S precision) (entry S precision i).row
    (entry S precision i).column : ℝ) = _
  rw [RationalCode.entrySum_at_entry _ (sourceSquareEntries_nodup S precision) _ (entry_mem S precision i)]

def edgeAt (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    PositiveEdges.Edge (SourcePositive.sourceH S precision) :=
  ⟨pair S precision i, by
    rw [sourceH_pair]
    exact_mod_cast sourceSquareEntries_nonzero S precision _ (entry_mem S precision i)⟩

theorem edgeAt_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (edgeAt S precision) := by
  intro i j h
  have hk := congrArg (fun e : PositiveEdges.Edge (SourcePositive.sourceH S precision) =>
    (e.val.1.val, e.val.2.val)) h
  have he : ((sourceSquareEntries S precision).map RationalCode.Entry.key).get
      ⟨i.val, by simp⟩ =
    ((sourceSquareEntries S precision).map RationalCode.Entry.key).get
      ⟨j.val, by simp⟩ := by
    simpa [edgeAt, pair, entry, RationalCode.Entry.key] using hk
  have hi := (sourceSquareEntries_nodup S precision).injective_get he
  exact Fin.ext (congrArg (fun k : Fin ((sourceSquareEntries S precision).map
    RationalCode.Entry.key).length => k.val) hi)

theorem edge_key_mem (S : Source.SparseSystem) (precision : ℕ)
    (e : PositiveEdges.Edge (SourcePositive.sourceH S precision)) :
    (e.val.1.val, e.val.2.val) ∈ (sourceSquareEntries S precision).map RationalCode.Entry.key := by
  apply (RationalCode.entrySum_nonzero_iff _ (sourceSquareEntries_nodup S precision)
    (sourceSquareEntries_nonzero S precision) _ _).mp
  rw [sourceSquareEntries_matrix]
  intro h
  apply e.property
  change (sourceSquareMap S precision).toMatrix' e.val.1 e.val.2 = 0
  rw [← sourceSquareMatrixQ_cast, h]
  norm_num

theorem edgeAt_surjective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Surjective (edgeAt S precision) := by
  intro e
  obtain ⟨a, ha, hk⟩ := List.mem_map.mp (edge_key_mem S precision e)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change ((sourceSquareEntries S precision).get i).row = e.val.1.val
    rw [hi]
    exact congrArg Prod.fst hk
  · apply Fin.ext
    change ((sourceSquareEntries S precision).get i).column = e.val.2.val
    rw [hi]
    exact congrArg Prod.snd hk

def edgeIndex (S : Source.SparseSystem) (precision : ℕ)
    (e : PositiveEdges.Edge (SourcePositive.sourceH S precision)) :
    Fin (sourceSquareEntries S precision).length :=
  ⟨((sourceSquareEntries S precision).map RationalCode.Entry.key).idxOf
      (e.val.1.val, e.val.2.val), by
    simpa using List.idxOf_lt_length_iff.mpr (edge_key_mem S precision e)⟩

theorem edgeIndex_edgeAt (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    edgeIndex S precision (edgeAt S precision i) = i := by
  apply Fin.ext
  have h := (sourceSquareEntries_nodup S precision).idxOf_getElem
    (i.val) (by simp)
  simpa [edgeIndex, edgeAt, pair, entry, RationalCode.Entry.key] using h

def edgeEquiv (S : Source.SparseSystem) (precision : ℕ) :
    Fin (sourceSquareEntries S precision).length ≃
      PositiveEdges.Edge (SourcePositive.sourceH S precision) where
  toFun := edgeAt S precision
  invFun := edgeIndex S precision
  left_inv := edgeIndex_edgeAt S precision
  right_inv e := by
    obtain ⟨i, rfl⟩ := edgeAt_surjective S precision e
    rw [edgeIndex_edgeAt]

def vertexEquiv (S : Source.SparseSystem) (precision : ℕ) :
    SourcePositive.Vertex S precision ≃
      Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length) :=
  (finSumFinEquiv.sumCongr (edgeEquiv S precision).symm).trans finSumFinEquiv

def positiveEdgeEquiv (S : Source.SparseSystem) (precision : ℕ) :
    (PositiveEdges.Edge (SourcePositive.sourceH S precision) ⊕
      PositiveEdges.Edge (SourcePositive.sourceH S precision)) ≃
      Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) :=
  ((edgeEquiv S precision).symm.sumCongr (edgeEquiv S precision).symm).trans finSumFinEquiv

theorem edge_count (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (PositiveEdges.Edge (SourcePositive.sourceH S precision)) =
      (sourceSquareEntries S precision).length := by
  simpa using (Fintype.card_congr (edgeEquiv S precision)).symm

theorem vertex_count (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (SourcePositive.Vertex S precision) =
      (sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length := by
  simpa using Fintype.card_congr (vertexEquiv S precision)

/-- Direct finite-coordinate endpoint arithmetic. The emitted positive edge
index already identifies its matrix entry; no support search is performed. -/
def positiveEndpoint (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (side : Bool) : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length) :=
  match finSumFinEquiv.symm i with
  | Sum.inl k =>
      if side then finSumFinEquiv (Sum.inr k)
      else finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl (pair S precision k).1)))
  | Sum.inr k =>
      if side then finSumFinEquiv (Sum.inr k)
      else finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr (pair S precision k).2)))

def positivePart (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)) : Bool :=
  decide ((sourceCircuit S precision).size + (sourceCircuit S precision).size ≤ v.val)

theorem positivePart_endpoint (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (side : Bool) : positivePart S precision (positiveEndpoint S precision i side) = side := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  cases k with
  | inl k =>
      cases side <;>
        simp only [positiveEndpoint, Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]
      · change decide (_ + _ ≤ (pair S precision k).1.val) = false
        simp only [decide_eq_false_iff_not]
        have h := (pair S precision k).1.isLt
        omega
      · change decide (_ + _ ≤ _ + _ + k.val) = true
        simp
  | inr k =>
      cases side <;>
        simp only [positiveEndpoint, Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]
      · change decide (_ + _ ≤ _ + (pair S precision k).2.val) = false
        simp only [decide_eq_false_iff_not]
        have h := (pair S precision k).2.isLt
        omega
      · change decide (_ + _ ≤ _ + _ + k.val) = true
        simp

theorem positiveEndpoint_correct (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (side : Bool) :
    positiveEndpoint S precision i side = vertexEquiv S precision
      (if side then (SourcePositive.graph S precision).head ((positiveEdgeEquiv S precision).symm i)
        else (SourcePositive.graph S precision).tail ((positiveEdgeEquiv S precision).symm i)) := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  cases k <;> cases side <;>
    simp only [positiveEndpoint, positiveEdgeEquiv, vertexEquiv, Equiv.trans_apply,
      Equiv.symm_trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Equiv.sumCongr_symm, Equiv.symm_symm, Sum.map_inl, Sum.map_inr,
      Bool.false_eq_true, ↓reduceIte, SourcePositive.graph, PositiveEdges.positiveGraph,
      Sum.elim_inl, Sum.elim_inr]
  · rfl
  · change _ = finSumFinEquiv (Sum.inr (edgeIndex S precision (edgeAt S precision _)))
    rw [edgeIndex_edgeAt]
  · rfl
  · change _ = finSumFinEquiv (Sum.inr (edgeIndex S precision (edgeAt S precision _)))
    rw [edgeIndex_edgeAt]

end Maxwell.Composition.SourceEnumeration
