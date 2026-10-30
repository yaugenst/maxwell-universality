import Maxwell.Continuum.SourceGeometryPacking
import Maxwell.Continuum.StoredGeometryReadPlan

/-! Exact indexed decoding of the packed chronological geometry. Offsets
are prefix lengths, so no search over pairs of vertices occurs. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
open Maxwell.Continuum.GeometryOutput
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def listValue (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

theorem arrayValue_packed {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : ℕ) :
    arrayValue (packedVector saved) i=listValue (packed saved) i := by
  by_cases hi : i<packedLength saved
  · have hi' : i<(packed saved).length := by simpa only [packed_length] using hi
    simp only [arrayValue,dite_eq_left hi,listValue,List.getElem?_eq_getElem hi',Option.getD_some,
      packedVector,Vector.get,List.getElem_toArray]
    rfl
  · have hi' : (packed saved).length ≤ i := by rw [packed_length];omega
    simp only [arrayValue,dite_eq_right hi,listValue,List.getElem?_eq_none hi',Option.getD_none]

theorem listValue_append_left (xs ys : List ℕ) (i : ℕ) (hi : i<xs.length) :
    listValue (xs++ys) i=listValue xs i := by
  simp only [listValue,List.getElem?_append_left hi]

theorem listValue_append_right (xs ys : List ℕ) (i : ℕ) :
    listValue (xs++ys) (xs.length+i)=listValue ys i := by
  simp only [listValue,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

theorem triples_lookup (xs : List Point) (i : ℕ) (hi : i<xs.length) (j : Fin 3) :
    listValue (xs.flatMap pointWords) (3*i+j.val)=listValue (pointWords xs[i]) j.val := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero]
      exact listValue_append_left _ _ _ (by rw [pointWords_length];exact j.isLt)
    | succ i =>
      have hix : i<xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [show 3*(i+1)+j.val=(pointWords x).length+(3*i+j.val) by rw [pointWords_length];omega,
        listValue_append_right]
      exact ih i hix

def pathOffset {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : ℕ) : ℕ :=
  3*v+(((List.finRange e).take i).flatMap (fun a=>pathWords (saved.paths.get a))).length

theorem original_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin v) (j : Fin 3) :
    arrayValue (packedVector saved) (3*i.val+j.val)=listValue (pointWords (saved.original.get i)) j.val := by
  rw [arrayValue_packed]
  unfold packed
  rw [listValue_append_left _ _ _ (by rw [triples_length,List.length_ofFn];omega)]
  rw [triples_lookup _ i.val (by rw [List.length_ofFn];exact i.isLt)]
  simp only [List.getElem_ofFn]

theorem path_decomposition {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e) :
    packed saved=
      ((List.ofFn saved.original.get).flatMap pointWords++
        ((List.finRange e).take i.val).flatMap (fun a=>pathWords (saved.paths.get a)))++
      pathWords (saved.paths.get i)++
        ((List.finRange e).drop (i.val+1)).flatMap (fun a=>pathWords (saved.paths.get a)) := by
  have hi : i.val<(List.finRange e).length := by simpa only [List.length_finRange] using i.isLt
  have hl : List.finRange e=(List.finRange e).take i.val++
      (List.finRange e)[i.val]::(List.finRange e).drop (i.val+1) := by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  conv_lhs => unfold packed;rw [hl]
  simp only [List.flatMap_append,List.flatMap_cons,List.getElem_finRange,List.append_assoc]
  rfl

theorem path_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e)
    (k : ℕ) (hk : k<(pathWords (saved.paths.get i)).length) :
    arrayValue (packedVector saved) (pathOffset saved i.val+k)=
      listValue (pathWords (saved.paths.get i)) k := by
  rw [arrayValue_packed,path_decomposition saved i]
  rw [List.append_assoc]
  have hpre : ((List.ofFn saved.original.get).flatMap pointWords++
        ((List.finRange e).take i.val).flatMap (fun a=>pathWords (saved.paths.get a))).length=
      pathOffset saved i.val := by simp only [List.length_append,triples_length,List.length_ofFn,pathOffset]
  rw [←hpre,listValue_append_right,listValue_append_left _ _ _ hk]

theorem path_length_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e) :
    arrayValue (packedVector saved) (pathOffset saved i.val)=(saved.paths.get i).length := by
  have h := path_lookup saved i 0 (by simp only [pathWords_length];omega)
  simpa only [Nat.add_zero,pathWords,listValue,List.getElem?_cons_zero,Option.getD_some] using h

theorem path_point_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e)
    (k : ℕ) (hk : k<(saved.paths.get i).length) (j : Fin 3) :
    arrayValue (packedVector saved) (pathOffset saved i.val+1+3*k+j.val)=
      listValue (pointWords (saved.paths.get i)[k]) j.val := by
  rw [show pathOffset saved i.val+1+3*k+j.val=pathOffset saved i.val+(1+(3*k+j.val)) by omega]
  rw [path_lookup saved i _ (by rw [pathWords_length];omega)]
  change listValue ([((saved.paths.get i).length)]++(saved.paths.get i).flatMap pointWords)
    (1+(3*k+j.val))=_
  rw [show 1+(3*k+j.val)=[((saved.paths.get i).length)].length+(3*k+j.val) by rfl,
    listValue_append_right,triples_lookup _ k hk]

#print axioms original_lookup
#print axioms path_point_lookup
end Maxwell.Composition.SourceDecorationEnumeration
