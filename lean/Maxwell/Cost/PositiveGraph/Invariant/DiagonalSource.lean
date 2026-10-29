import Maxwell.Cost.PositiveGraph.Invariant.DiagonalSum
import Maxwell.Cost.PositiveGraph.Invariant.EndpointSource
import Maxwell.Cost.PositiveGraph.Initialize.Zeros

namespace Maxwell.Cost.PositiveGraph.Invariant
open Maxwell.Logical
open scoped BigOperators

theorem source_contribution (S : Source.SparseSystem) (p : ℕ)
    (k : Fin (sourceSquareEntries S p).length)
    (i : Fin ((sourceCircuit S p).size+(sourceCircuit S p).size+(sourceSquareEntries S p).length)) :
    (contribution (sourceCircuit S p).size k.val (Composition.SourceEnumeration.entry S p k) i.val : ℚ) =
    2*RationalScatter.sumAt (Composition.PositiveScatter.term (Composition.SourceEnumeration.pair S p k)
      (Composition.SourceEnumeration.entry S p k).value k) i := by
  have hflag := SparseEmission.source_flag_value S p (Composition.SourceEnumeration.entry S p k)
    (Composition.SourceEnumeration.entry_mem S p k)
  simp only [contribution,Int.cast_add,Int.cast_ite,Int.cast_zero,
    endpointDelta_value,mediatorDelta_value,hflag]
  simp only [RationalScatter.sumAt,Composition.PositiveScatter.term,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Fin.ext_iff,Composition.SourceEnumeration.pair]
  simp only [finSumFinEquiv,Equiv.coe_fn_mk,Sum.elim,Fin.val_natAdd,Fin.val_castAdd]
  rw [show 2*(sourceCircuit S p).size=(sourceCircuit S p).size+(sourceCircuit S p).size by omega]
  change
    (if (Composition.SourceEnumeration.entry S p k).row=i.val then -2*(Composition.SourceEnumeration.entry S p k).value else 0)+
    (if (sourceCircuit S p).size+(Composition.SourceEnumeration.entry S p k).column=i.val then -2*(Composition.SourceEnumeration.entry S p k).value else 0)+
    (if (sourceCircuit S p).size+(sourceCircuit S p).size+k.val=i.val then -2*(Composition.SourceEnumeration.entry S p k).value⁻¹ else 0) =
    2*((if (Composition.SourceEnumeration.entry S p k).row=i.val then -(Composition.SourceEnumeration.entry S p k).value else 0)+
    ((if (sourceCircuit S p).size+(Composition.SourceEnumeration.entry S p k).column=i.val then -(Composition.SourceEnumeration.entry S p k).value else 0)+
    ((if (sourceCircuit S p).size+(sourceCircuit S p).size+k.val=i.val then -(Composition.SourceEnumeration.entry S p k).value⁻¹ else 0)+0)))
  split_ifs <;> ring

theorem source_contributions_eq (S : Source.SparseSystem) (p i : ℕ) :
    (sourceRecords S p).mapIdx (fun j e => contribution (sourceCircuit S p).size j e.val i) =
    (sourceSquareEntries S p).mapIdx (fun j e => contribution (sourceCircuit S p).size j e i) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_mapIdx]
    rw [sourceRecords_get]

theorem source_contribution_sum (S : Source.SparseSystem) (p : ℕ)
    (i : Fin ((sourceCircuit S p).size+(sourceCircuit S p).size+(sourceSquareEntries S p).length)) :
    (((sourceRecords S p).mapIdx fun j e => contribution (sourceCircuit S p).size j e.val i.val).sum : ℚ) =
    2*Composition.PositiveRational.diagonal S p i := by
  rw [source_contributions_eq,List.mapIdx_eq_ofFn,List.sum_ofFn]
  simp only [Int.cast_sum]
  rw [←Composition.PositiveScatter.updates_correct,Composition.PositiveScatter.sumAt_updates,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact source_contribution S p k i

theorem source_integer_final (S : Source.SparseSystem) (p : ℕ)
    (i : Fin (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length)) :
    (integerFold (sourceCircuit S p).size (sourceSquareEntries S p).length 0 (sourceRecords S p)
      (by simp) (Vector.replicate _ 0)).get i =
    (Composition.PositiveScatter.numerator S p).get (Fin.cast (by omega) i) := by
  have h := integerFold_get (sourceCircuit S p).size (sourceSquareEntries S p).length 0
    (sourceRecords S p) (by simp) (Vector.replicate _ 0) i
  have hz : (Vector.replicate (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) (0:ℤ)).get i=0 := by simp [Vector.get,Fin.cast]
  simp only [hz,zero_add] at h
  apply Int.cast_injective (α := ℚ)
  rw [h]
  have hs := source_contribution_sum S p (Fin.cast (by omega) i)
  simp only [Fin.val_cast] at hs
  have hn := Composition.PositiveScatter.numerator_exact S p (Fin.cast (by omega) i)
  rw [Composition.PositiveScatter.diagonal_get] at hn
  change _=(_ : ℚ)
  linarith

def sourceDiagonalWords (S : Source.SparseSystem) (p : ℕ) :
    Vector (List Bool) (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) :=
  Vector.ofFn fun i => FixedWidth.bits 4
    (diagonalCode ((Composition.PositiveScatter.numerator S p).get (Fin.cast (by omega) i))).bits

theorem source_diagonal_exact (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length)
    (hinit : initial.diagonal=Initialize.constantWords (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) 4 8) :
    (sourceTables W S p initial).diagonal=sourceDiagonalWords S p := by
  have hz : initial.diagonal=diagonalWords (Vector.replicate _ 0) := by
    rw [hinit]
    apply Vector.ext
    intro i hi
    simp [Initialize.constantWords,diagonalWords,diagonalCode]
  rw [sourceTables,fold_diagonal_encoded W _ _ _ _ _ _ _ hz]
  apply Vector.ext
  intro j hj
  let i : Fin (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) := ⟨j,hj⟩
  change (diagonalWords _).get i=(sourceDiagonalWords S p).get i
  rw [diagonalWords_get,source_integer_final]
  simp [sourceDiagonalWords,Vector.get,Fin.cast]

end Maxwell.Cost.PositiveGraph.Invariant
