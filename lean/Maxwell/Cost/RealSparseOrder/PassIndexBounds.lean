import Maxwell.Cost.RealSparseOrder.IndexBounds
import Maxwell.Cost.RealSparseOrder.PassState
import Maxwell.Cost.RealSparseOrder.PassSetup
import Maxwell.Cost.RealSparseOrder.OuterControl

namespace Maxwell.Cost.RealSparseOrder
open RealSimulation.IndexWidth

theorem passSetup_index_bound {B : ℕ} {s : RAMState} {src dst : Buffer} {width remaining : ℕ}
    (h : Pass.Config s src dst width remaining) (hs : IndexBound B s)
    (ha : Within B src remaining) (hsize : 2*remaining≤B) :
    IndexBound B (PassSetup.initialized s) := by
  have hl : PassSetup.leftSize s≤remaining := by
    simp only [PassSetup.leftSize,h.width,h.remaining]
    exact min_le_right _ _
  have hr : PassSetup.rightSize s≤remaining-PassSetup.leftSize s := by
    simp only [PassSetup.rightSize,h.remaining]
    exact min_le_right _ _
  have hremaining : remaining≤B := by simpa only [h.remaining] using hs 17
  have hlB : PassSetup.leftSize s≤B := hl.trans hremaining
  have hrB : PassSetup.rightSize s≤B := by omega
  have hsum : PassSetup.leftSize s+PassSetup.rightSize s≤remaining := by omega
  have hsumB : PassSetup.leftSize s+PassSetup.rightSize s≤B := hsum.trans hremaining
  have hdouble : (PassSetup.leftSize s+PassSetup.rightSize s)+
      (PassSetup.leftSize s+PassSetup.rightSize s)≤B := by omega
  have hrow : s.indices 19+PassSetup.leftSize s+PassSetup.leftSize s≤B := by
    rw [h.sourceRow]
    have hh := ha.1
    omega
  have hvalue : s.indices 20+PassSetup.leftSize s≤B := by
    rw [h.sourceValue]
    have hh := ha.2
    omega
  have hselected : IndexBound B (PassSetup.selected s) := by
    unfold PassSetup.selected
    exact ((hs.setIndex 3 _ hlB).setIndex 12 _ ((Nat.sub_le _ _).trans (hs 17))).setIndex 4 _ hrB
  unfold PassSetup.initialized
  exact (((((((((hselected.setIndex 5 _ hsumB).setIndex 24 _ hsumB).setIndex 25 _ hdouble).setIndex 6 _ (hs 19)).setIndex 7 _ (hs 20)).setIndex 8 _ (by omega)).setIndex 8 _ hrow).setIndex 9 _ hvalue).setIndex 10 _ (hs 21)).setIndex 11 _ (hs 22)

theorem passAdvance_index_bound {B : ℕ} {s : RAMState} {src dst : Buffer}
    {width remaining count : ℕ} (h : Pass.Config s src dst width remaining)
    (hs : IndexBound B s) (ha : Within B src remaining) (ho : Within B dst remaining)
    (hc : s.indices 24=count) (hc2 : s.indices 25=2*count) (hle : count≤remaining) :
    IndexBound B (PassAdvance.advanced s) := by
  have hsr : s.indices 19+s.indices 25≤B := by rw [h.sourceRow,hc2]; have hh:=ha.1; omega
  have hsv : s.indices 20+s.indices 24≤B := by rw [h.sourceValue,hc]; have hh:=ha.2; omega
  have htr : s.indices 21+s.indices 25≤B := by rw [h.targetRow,hc2]; have hh:=ho.1; omega
  have htv : s.indices 22+s.indices 24≤B := by rw [h.targetValue,hc]; have hh:=ho.2; omega
  unfold PassAdvance.advanced
  exact ((((hs.setIndex 17 _ ((Nat.sub_le _ _).trans (hs 17))).setIndex 19 _ hsr).setIndex 20 _ hsv).setIndex 21 _ htr).setIndex 22 _ htv

theorem outerPrepare_index_bound {B : ℕ} {s : RAMState} (hs : IndexBound B s) :
    IndexBound B (OuterControl.prepared s) := by
  unfold OuterControl.prepared
  exact ((((hs.setIndex 17 _ (hs 26)).setIndex 19 _ (hs 27)).setIndex 20 _ (hs 28)).setIndex 21 _ (hs 29)).setIndex 22 _ (hs 30)

theorem outerAdvance_index_bound {B : ℕ} {s : RAMState}
    (hs : IndexBound B s) (hw : 2*s.indices 18≤B) :
    IndexBound B (OuterControl.advanced s) := by
  unfold OuterControl.advanced
  exact ((((((hs.setIndex 31 _ (hs 27)).setIndex 27 _ (hs 29)).setIndex 29 _ (hs 27)).setIndex 31 _ (hs 28)).setIndex 28 _ (hs 30)).setIndex 30 _ (hs 28)).setIndex 18 _ (by omega)

end Maxwell.Cost.RealSparseOrder
