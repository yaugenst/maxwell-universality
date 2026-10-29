import Maxwell.Composition.SourceCached
import Maxwell.Composition.PositiveGraph

/-! Exact rational diagonal data for the indexed positive graph. These
coefficients are computed from the finite emitted source-circuit entries. -/

namespace Maxwell.Composition.PositiveRational
open Maxwell.Logical

def incidence (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin (sourceCircuit S precision).size ⊕ Fin (sourceCircuit S precision).size)
    (k : Fin (sourceSquareEntries S precision).length) : ℚ :=
  match v with
  | .inl i => if i = (SourceEnumeration.pair S precision k).1 then 1 else 0
  | .inr j => if j = (SourceEnumeration.pair S precision k).2 then 1 else 0

theorem incidence_cast (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin (sourceCircuit S precision).size ⊕ Fin (sourceCircuit S precision).size)
    (k : Fin (sourceSquareEntries S precision).length) :
    (incidence S precision v k : ℝ) =
      (PositiveEdges.graph (SourcePositive.sourceH S precision)).incidence v
        (SourceEnumeration.edgeEquiv S precision k) := by
  cases v <;>
    simp only [incidence, PositiveEdges.graph, SignedIncidence.incidence,
      SourceEnumeration.edgeEquiv, SourceEnumeration.edgeAt, Equiv.coe_fn_mk,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte]
  all_goals split_ifs <;> norm_num

def endpointDiagonal (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin (sourceCircuit S precision).size ⊕ Fin (sourceCircuit S precision).size) : ℚ :=
  -∑ k, incidence S precision v k * (SourceEnumeration.entry S precision k).value

theorem endpointDiagonal_cast (S : Source.SparseSystem) (precision : ℕ)
    (v : Fin (sourceCircuit S precision).size ⊕ Fin (sourceCircuit S precision).size) :
    (endpointDiagonal S precision v : ℝ) =
      PositiveEdges.endpointDiagonal (SourcePositive.sourceH S precision) v := by
  rw [endpointDiagonal, Rat.cast_neg, Rat.cast_sum, PositiveEdges.endpointDiagonal]
  congr 1
  rw [← (SourceEnumeration.edgeEquiv S precision).sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Rat.cast_mul, incidence_cast]
  congr 1
  exact (SourceEnumeration.sourceH_pair S precision k).symm

def diagonal (S : Source.SparseSystem) (precision : ℕ) :
    Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length) → ℚ := fun i =>
  match finSumFinEquiv.symm i with
  | .inl v => endpointDiagonal S precision (finSumFinEquiv.symm v)
  | .inr k => -((SourceEnumeration.entry S precision k).value)⁻¹

theorem diagonal_cast (S : Source.SparseSystem) (precision : ℕ)
    (v : SourcePositive.Vertex S precision) :
    (diagonal S precision (SourceEnumeration.vertexEquiv S precision v) : ℝ) =
      PositiveEdges.diagonal (SourcePositive.sourceH S precision) v := by
  cases v with
  | inl v =>
      simp only [diagonal, SourceEnumeration.vertexEquiv, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, PositiveEdges.diagonal,
        Sum.elim_inl]
      exact endpointDiagonal_cast S precision v
  | inr e =>
      obtain ⟨k, rfl⟩ := (SourceEnumeration.edgeEquiv S precision).surjective e
      simp only [diagonal, SourceEnumeration.vertexEquiv, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, PositiveEdges.diagonal,
        Sum.elim_inr, Rat.cast_neg, Rat.cast_inv]
      congr 2
      exact (SourceEnumeration.sourceH_pair S precision k).symm

end Maxwell.Composition.PositiveRational
