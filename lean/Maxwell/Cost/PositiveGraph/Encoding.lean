import Maxwell.Composition.SourceRouting
import Maxwell.Composition.PositiveScatter
import Maxwell.Cost.SparseEmission.Values

namespace Maxwell.Cost.PositiveGraph
open Maxwell.Logical Maxwell.Logical.Routing

/-- The actual array slot of each side of an indexed positive edge. -/
theorem incidence_slot (edges : ℕ) (edge : Fin edges) (side : Bool) :
    (Gluing.incidenceIndex edges (edge,side)).val = 2*edge.val+side.toNat := by
  cases side <;> simp [Gluing.incidenceIndex,finTwoEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem row_endpoint {d count : ℕ} (pair : Fin count → Fin d × Fin d) (k : Fin count) :
    (Composition.SourceCached.endpointFromPairs d count pair (finSumFinEquiv (.inl k)) false).val =
      (pair k).1.val := by
  simp only [Composition.SourceCached.endpointFromPairs,Equiv.symm_apply_apply]
  rfl

theorem column_endpoint {d count : ℕ} (pair : Fin count → Fin d × Fin d) (k : Fin count) :
    (Composition.SourceCached.endpointFromPairs d count pair (finSumFinEquiv (.inr k)) false).val =
      d+(pair k).2.val := by
  simp only [Composition.SourceCached.endpointFromPairs,Equiv.symm_apply_apply]
  simp [Nat.add_comm]

theorem mediator_endpoint {d count : ℕ} (pair : Fin count → Fin d × Fin d) (k : Fin count) (right : Bool) :
    (Composition.SourceCached.endpointFromPairs d count pair
      (finSumFinEquiv (if right then Sum.inr k else Sum.inl k)) true).val = 2*d+k.val := by
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte,
    Composition.SourceCached.endpointFromPairs,Equiv.symm_apply_apply]
    <;> simp [two_mul,Nat.add_comm]

def endpointDelta (negative half : Bool) : ℤ :=
  (if negative then 1 else -1)*(if half then 1 else 2)
def mediatorDelta (negative half : Bool) : ℤ :=
  (if negative then 1 else -1)*(if half then 4 else 2)

theorem endpointDelta_value (negative half : Bool) :
    (endpointDelta negative half : ℚ) = -2*SparseEmission.flagValue negative half := by
  cases negative <;> cases half <;> norm_num [endpointDelta,SparseEmission.flagValue]

theorem mediatorDelta_value (negative half : Bool) :
    (mediatorDelta negative half : ℚ) = -2*(SparseEmission.flagValue negative half)⁻¹ := by
  cases negative <;> cases half <;> norm_num [mediatorDelta,SparseEmission.flagValue]

/-- Four physical bits represent the signed half-integer diagonal through
an offset of eight. Modulo arithmetic is exact even during sparse scatter. -/
def diagonalCode (numerator : ℤ) : ℕ := ((8+numerator)%16).toNat

theorem diagonalCode_lt (numerator : ℤ) : diagonalCode numerator < 16 := by
  have hn := Int.emod_nonneg (8+numerator) (by norm_num : (16:ℤ) ≠ 0)
  have hl := Int.emod_lt_of_pos (8+numerator) (by norm_num : (0:ℤ) < 16)
  unfold diagonalCode
  omega

theorem diagonalCode_exact (numerator : ℤ) (h : |numerator| ≤ 6) :
    (diagonalCode numerator : ℤ) = 8+numerator := by
  obtain ⟨lo,hi⟩ := abs_le.mp h
  simp [diagonalCode,Int.emod_eq_of_lt (by omega : 0 ≤ 8+numerator) (by omega : 8+numerator < 16),
    Int.toNat_of_nonneg (by omega : 0 ≤ 8+numerator)]

theorem source_diagonal_code (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((Logical.sourceCircuit S precision).size+(Logical.sourceCircuit S precision).size+
      (Logical.sourceSquareEntries S precision).length)) :
    ((diagonalCode ((Composition.PositiveScatter.numerator S precision).get i) : ℤ)-8 : ℚ)/2 =
      Composition.PositiveRational.diagonal S precision i := by
  rw [diagonalCode_exact _ (Composition.PositiveScatter.numerator_abs_le_six S precision i)]
  norm_num only [Int.cast_add,Int.cast_ofNat,add_sub_cancel_left]
  rw [Composition.PositiveScatter.numerator_exact,Composition.PositiveScatter.diagonal_get]

end Maxwell.Cost.PositiveGraph
