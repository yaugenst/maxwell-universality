import Maxwell.Cost.RealSparseOrder.Relabel
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control RealSimulation.IndexWidth

theorem loaded_index_bound {B : ℕ} {s : RAMState} (hs : IndexBound B s) :
    IndexBound B (loaded s) := hs.setIndex 37 _ (hs _)

theorem created_index_bound (input : RAMInput) {B : ℕ} {s : RAMState}
    (hs : IndexBound B s) (h1 : 1≤B)
    (hm : s.indices 40+s.indices 35≤B) (hv : s.indices 41+s.indices 35≤B)
    (hi : s.indices 26+s.indices 37≤B) (hc : s.indices 35+1≤B) :
    IndexBound B (created input s) := by
  unfold created
  exact ((((((hs.setIndex 38 _ hm).setIndex (s.indices 40+s.indices 35) _ (hs 37)).setIndex 39 _ hi).setIndex 38 _ hv).setIndex 34 _ (hs 37)).setIndex 35 _ hc).setIndex 36 _ h1

theorem rewritten_index_bound {B : ℕ} {s : RAMState}
    (hs : IndexBound B s) (hc : s.indices 33+2≤B) : IndexBound B (rewritten s) := by
  have hn : s.indices 35-1≤B := (Nat.sub_le _ _).trans (hs 35)
  unfold rewritten
  exact (((hs.setIndex 37 _ hn).setIndex (s.indices 33) _ hn).setIndex 33 _ hc).setIndex 32 _ ((Nat.sub_le _ _).trans (hs 32))

theorem chosen_index_bound (input : RAMInput) {B : ℕ} {s : Store}
    (previous : Option ℕ) (row : ℕ) (hs : IndexBound B s.val) (h1 : 1≤B)
    (hm : s.val.indices 40+s.val.indices 35≤B) (hv : s.val.indices 41+s.val.indices 35≤B)
    (hi : s.val.indices 26+s.val.indices 37≤B) (hc : s.val.indices 35+1≤B) :
    IndexBound B (chosen input previous row s).val := by
  unfold chosen
  split
  · exact hs
  · exact created_index_bound input hs h1 hm hv hi hc

theorem processed_index_bound (input : RAMInput) {B : ℕ} {s : Store} {b : Buffer}
    {remaining : ℕ} {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs) (hs : IndexBound B s.val)
    (hmap : 100≤map) (hc : b.coordinates+2≤B)
    (hm : map+count≤B) (hv : rhs+count≤B) (hi : m+row≤B) (hn : count+1≤B)
    (hr : s.val.indices b.coordinates=row) :
    IndexBound B (processed input previous row s).val := by
  let mid := Store.ofState (loaded s.val)
  have hmconfig : Config mid.val b remaining previous count m map rhs :=
    (config_ofState _ _ _ _ _ _ _ _).mpr h.loaded
  have hms : IndexBound B mid.val := loaded_index_bound hs
  have hrow : mid.val.indices 37=row := by
    simp [mid,Store.ofState,loaded,RAMState.setIndex,h.cursor,hr]
  have hchosen : IndexBound B (chosen input previous row mid).val :=
    chosen_index_bound input previous row hms (by simpa only [h.one] using hs 1)
      (by simpa only [hmconfig.mapBase,hmconfig.count] using hm)
      (by simpa only [hmconfig.rhsBase,hmconfig.count] using hv)
      (by simpa only [hmconfig.originalCount,hrow] using hi)
      (by simpa only [hmconfig.count] using hn)
  apply rewritten_index_bound hchosen
  rw [(hmconfig.chosen hmap hrow).cursor]
  exact hc

theorem initialized_index_bound {B : ℕ} {s : RAMState} (hs : IndexBound B s)
    (hb : outputBase (s.indices 26)≤B) : IndexBound B (initialized s) := by
  have hdouble : s.indices 26+s.indices 26≤B := by unfold outputBase at hb; omega
  have hquad : s.indices 26+s.indices 26+(s.indices 26+s.indices 26)≤B := by
    unfold outputBase at hb; omega
  have h100 : 100≤B := by unfold outputBase at hb; omega
  unfold initialized
  exact (((((((((hs.setIndex 32 _ (hs 26)).setIndex 33 _ (hs 27)).setIndex 34 _ (Nat.zero_le _)).setIndex 35 _ (Nat.zero_le _)).setIndex 36 _ (Nat.zero_le _)).setIndex 40 _ hdouble).setIndex 40 _ hquad).setIndex 41 _ h100).setIndex 40 _ hb).setIndex 41 _ hb

end Maxwell.Cost.RealSparseOrder.Relabel
