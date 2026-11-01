import Mathlib.Data.List.FinRange

/-! Direct indexing into a chronological concatenation of finite blocks.
The block offset is the length of the preceding blocks, without a search. -/
namespace Maxwell.ListBlocks

theorem getElem?_flatMap {α β : Type*} (xs : List α) (f : α→List β)
    (i : ℕ) (hi : i<xs.length) (j : ℕ) (hj : j<(f xs[i]).length) :
    (xs.flatMap f)[((xs.take i).flatMap f).length+j]?=some (f xs[i])[j] := by
  have split : xs=xs.take i++xs[i]::xs.drop (i+1) := by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have blocks : xs.flatMap f=(xs.take i).flatMap f++f xs[i]++(xs.drop (i+1)).flatMap f := by
    conv_lhs => rw [split]
    simp only [List.flatMap_append,List.flatMap_cons,List.append_assoc]
  rw [blocks,List.append_assoc,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left,
    List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

theorem getElem?_finRange {α : Type*} {n : ℕ} (f : Fin n→List α) (i : Fin n)
    (j : ℕ) (hj : j<(f i).length) :
    ((List.finRange n).flatMap f)[(((List.finRange n).take i.val).map (fun k=>(f k).length)).sum+j]?=
      some (f i)[j] := by
  have hi : i.val<(List.finRange n).length := by simpa only [List.length_finRange] using i.isLt
  have element : (List.finRange n)[i.val]'hi=i := by
    simp only [List.getElem_finRange]
    exact Fin.ext rfl
  have h := getElem?_flatMap (List.finRange n) f i.val hi j (by rwa [element])
  simpa only [List.length_flatMap,element] using h

#print axioms getElem?_finRange
end Maxwell.ListBlocks
