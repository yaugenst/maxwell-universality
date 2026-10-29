import Maxwell.Cost.PositiveGraph.Invariant.Diagonal
import Mathlib.Data.List.Indexes

namespace Maxwell.Cost.PositiveGraph.Invariant

def contribution (d k : ℕ) (e : Logical.RationalCode.Entry) (i : ℕ) : ℤ :=
  let negative := decide (e.value<0)
  let half := decide (e.value=1/2 ∨ e.value= -1/2)
  (if e.row=i then endpointDelta negative half else 0)+
  (if d+e.column=i then endpointDelta negative half else 0)+
  (if 2*d+k=i then mediatorDelta negative half else 0)

private theorem triple_get {n : ℕ} (v : Vector ℤ n) (r c m : Fin n)
    (hrc : r ≠ c) (hrm : r ≠ m) (hcm : c ≠ m) (dr dc dm : ℤ) (i : Fin n) :
    (((v.set r (v.get r+dr)).set c (v.get c+dc)).set m (v.get m+dm)).get i =
    v.get i+(if r=i then dr else 0)+(if c=i then dc else 0)+(if m=i then dm else 0) := by
  by_cases hm : m=i
  · subst i
    simp only [Logical.Routing.DummyFill.get_set,hrm,hcm,↓reduceIte,add_zero]
  · by_cases hc : c=i
    · subst i
      simp only [Logical.Routing.DummyFill.get_set,hrc,hm,↓reduceIte,add_zero]
    · by_cases hr : r=i
      · subst i
        simp only [Logical.Routing.DummyFill.get_set,hc,hm,↓reduceIte,add_zero]
      · simp only [Logical.Routing.DummyFill.get_set,hr,hc,hm,↓reduceIte,add_zero]

theorem integerNext_get (d K k : ℕ) (hk : k<K) (e : BoundedEntry d)
    (values : Vector ℤ (2*d+K)) (i : Fin (2*d+K)) :
    (integerNext d K k hk e values).get i = values.get i+contribution d k e.val i.val := by
  have hr := e.property.1
  have hc := e.property.2
  have hrc : rowIndex d K e.val e.property.1 ≠ columnIndex d K e.val e.property.2 := by
    intro h; have hv := congrArg Fin.val h; dsimp [rowIndex,columnIndex] at hv; omega
  have hrm : rowIndex d K e.val e.property.1 ≠ mediatorIndex d K k hk := by
    intro h; have hv := congrArg Fin.val h; dsimp [rowIndex,mediatorIndex] at hv; omega
  have hcm : columnIndex d K e.val e.property.2 ≠ mediatorIndex d K k hk := by
    intro h; have hv := congrArg Fin.val h; dsimp [columnIndex,mediatorIndex] at hv; omega
  have h := triple_get values _ _ _ hrc hrm hcm
    (endpointDelta (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)))
    (endpointDelta (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)))
    (mediatorDelta (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2))) i
  simpa only [integerNext,contribution,DiagonalWord.delta,endpointDelta,mediatorDelta,
    Bool.false_eq_true,↓reduceIte,Fin.ext_iff,rowIndex,columnIndex,mediatorIndex,add_assoc] using h

theorem integerFold_get (d K start : ℕ) (entries : List (BoundedEntry d))
    (hfit : start+entries.length ≤ K) (values : Vector ℤ (2*d+K)) (i : Fin (2*d+K)) :
    (integerFold d K start entries hfit values).get i =
    values.get i+(entries.mapIdx fun j e => contribution d (start+j) e.val i.val).sum := by
  induction entries generalizing start values with
  | nil => simp [integerFold]
  | cons e rest ih =>
    rw [integerFold,ih,integerNext_get]
    simp only [List.mapIdx_cons,List.sum_cons,Nat.add_zero]
    rw [add_assoc]
    congr 2
    apply congrArg List.sum
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro j h
    congr 1
    omega

end Maxwell.Cost.PositiveGraph.Invariant
