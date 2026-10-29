import Maxwell.Cost.PositiveGraph.Fold
import Maxwell.Cost.PositiveGraph.Encoding

namespace Maxwell.Cost.PositiveGraph.Invariant

def slot (K k : ℕ) (hk : k<K) (right side : Bool) : Fin (4*K) :=
  ⟨2*((if right then K else 0)+k)+side.toNat,by cases right <;> cases side <;> simp <;> omega⟩

def endpointPayload (W d k : ℕ) (e : Logical.RationalCode.Entry) (right side : Bool) : List Bool :=
  if side then FixedWidth.bits (W+3) (2*d+k).bits else
  if right then FixedWidth.bits (W+3) (d+e.column).bits else
    FixedWidth.bits (W+3) (SourceCircuit.fixedWidth W e.row)

private theorem get_set {α : Type*} {n : ℕ} (v : Vector α n) (i : ℕ) (hi : i<n)
    (a : α) (j : Fin n) : (v.set i a hi).get j = if i=j.val then a else v.get j := by
  simp [Vector.get,Fin.cast,Array.getElem_set]

theorem nextEndpoints_slot (W d K index k : ℕ) (hi : index<K) (hk : k<K)
    (e : Logical.RationalCode.Entry) (v : Vector (List Bool) (4*K)) (right side : Bool) :
    (nextEndpoints W d K index hi e v).get (slot K k hk right side) =
      if index=k then endpointPayload W d k e right side else v.get (slot K k hk right side) := by
  by_cases h : index=k
  · subst index
    cases right <;> cases side
    all_goals dsimp only [slot,endpointPayload]
    all_goals simp only [nextEndpoints,Endpoints.setPair,get_set]
    all_goals simp only [Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,↓reduceIte,Nat.zero_add,Nat.add_zero]
    all_goals split_ifs <;> first | rfl | omega
  · cases right <;> cases side
    all_goals dsimp only [slot,endpointPayload]
    all_goals simp only [nextEndpoints,Endpoints.setPair,get_set,h]
    all_goals simp only [Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,↓reduceIte,Nat.zero_add,Nat.add_zero]
    all_goals split_ifs <;> first | rfl | omega

theorem fold_endpoints_prior (W d K start : ℕ) (entries : List (BoundedEntry d))
    (hfit : start+entries.length ≤ K) (tables : Tables d K) (k : ℕ) (hk : k<K)
    (hprior : k<start) (right side : Bool) :
    (foldTables W d K start entries hfit tables).endpoints.get (slot K k hk right side) =
      tables.endpoints.get (slot K k hk right side) := by
  induction entries generalizing start tables with
  | nil => rfl
  | cons e rest ih =>
    rw [foldTables,ih (start+1) _ _ (by omega)]
    change (nextEndpoints W d K start (by simp only [List.length_cons] at hfit; omega) e.val tables.endpoints).get _ = _
    rw [nextEndpoints_slot]; simp [show start ≠ k by omega]

theorem fold_endpoints_hit (W d K start : ℕ) (entries : List (BoundedEntry d))
    (hfit : start+entries.length ≤ K) (tables : Tables d K) (j : ℕ) (hj : j<entries.length)
    (right side : Bool) :
    (foldTables W d K start entries hfit tables).endpoints.get
      (slot K (start+j) (by omega) right side) =
    endpointPayload W d (start+j) (entries[j]'hj).val right side := by
  induction entries generalizing start tables j with
  | nil => simp at hj
  | cons e rest ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero,List.getElem_cons_zero]
      rw [foldTables,fold_endpoints_prior W d K (start+1) rest _ _ start (by simp only [List.length_cons] at hfit; omega) (by omega)]
      change (nextEndpoints W d K start (by simp only [List.length_cons] at hfit; omega) e.val tables.endpoints).get _ = _
      rw [nextEndpoints_slot]; simp
    | succ j =>
      have hjr : j<rest.length := by simpa using hj
      have h := ih (start+1) (by simp only [List.length_cons] at hfit; omega)
        (tables.next W d K start (by simp only [List.length_cons] at hfit; omega) e) j hjr
      simpa only [foldTables,List.getElem_cons_succ,Nat.add_succ,Nat.succ_add] using h

end Maxwell.Cost.PositiveGraph.Invariant
