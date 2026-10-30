import Maxwell.Continuum.SourceRoutingLabelStorage
import Maxwell.Continuum.SourceRoutingTreeMemory

/-! Actual zeroed memory gives the terminal recursive labels.  Forward
visits to earlier tree blocks preserve those bits. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Leaves
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def labelBase (heap rootCount rootWidth node n w : ℕ) : ℕ :=
  RoutingAllocator.slab (block heap rootCount rootWidth node) n w 10

theorem zero_labels (rows : ℕ) (target : Targets.Target rows 0)
    (memory : ℕ→Bool) (base width : ℕ)
    (hz : ∀p,base ≤ p→p<base+2^rows*width→memory p=false) :
    StoredLabels rows 0 target memory base width := by
  intro p j hj
  have hi : (ColorData.index rows 0 p).val<2^rows := by
    simpa only [Nat.zero_add] using (ColorData.index rows 0 p).isLt
  have hb:=Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  rw [hz _ (by omega) (by nlinarith only [hb,hj])]
  dsimp only
  simp [ColorData.labels_zero,IncidenceEncoding.word,FixedWidth.bits_empty]

theorem initialized (heap rootCount rootWidth total rows : ℕ)
    (hn : 2^rows ≤ rootCount) (hw : rows+1 ≤ rootWidth)
    (memory : ℕ→Bool)
    (hz : ∀p,heap ≤ p→p<heap+(2^(total+1)-1)*stride rootCount rootWidth→memory p=false)
    (i : Fin (2^total)) (target : Targets.Target rows 0) :
    StoredLabels rows 0 target memory
      (labelBase heap rootCount rootWidth (levelNode total i) (2^rows) (rows+1)) (rows+1) := by
  apply zero_labels
  intro p hlo hhi
  have fits:=slab_fits heap rootCount rootWidth (levelNode total i) (2^rows) (rows+1) 10 hn hw (by omega)
  have range:=level_range total i
  have last:=Nat.mul_le_mul_right (stride rootCount rootWidth) (Nat.succ_le_of_lt range.2)
  apply hz p
  · dsimp only [labelBase,block] at hlo
    dsimp only [block] at fits
    omega
  · dsimp only [labelBase,block] at hhi
    dsimp only [block] at fits
    nlinarith only [fits.2,last,hhi]

theorem preserve (heap rootCount rootWidth total rows first count : ℕ)
    (hn : 2^rows ≤ rootCount) (hw : rows+1 ≤ rootWidth)
    (hbefore : first+count ≤ 2^total-1)
    (before after : ℕ→Bool)
    (hf : Memory.Frame (block heap rootCount rootWidth first)
      (count*stride rootCount rootWidth) before after)
    (i : Fin (2^total)) (target : Targets.Target rows 0)
    (hs : StoredLabels rows 0 target before
      (labelBase heap rootCount rootWidth (levelNode total i) (2^rows) (rows+1)) (rows+1)) :
    StoredLabels rows 0 target after
      (labelBase heap rootCount rootWidth (levelNode total i) (2^rows) (rows+1)) (rows+1) := by
  apply IndexedMemory.same_memory _ _ before after _ _ _ hs
  intro p hlo _
  apply hf p (Or.inr ?_)
  have firstEnd:=Nat.mul_le_mul_right (stride rootCount rootWidth)
    (hbefore.trans (level_range total i).1)
  have fits:=slab_fits heap rootCount rootWidth (levelNode total i) (2^rows) (rows+1) 10 hn hw (by omega)
  dsimp only [labelBase,block] at hlo
  dsimp only [block] at fits ⊢
  nlinarith only [firstEnd,fits.1,hlo]

#print axioms initialized
#print axioms preserve
end Maxwell.Cost.RoutingPorts.Complete.Tree.Leaves
