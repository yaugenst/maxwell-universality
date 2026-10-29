import Maxwell.Cost.RealSparseOrder.PassLoop
import Maxwell.Cost.RealSparseOrder.OuterControl
import Maxwell.Cost.RealSparseOrder.PureSort

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control

structure Config (s : RAMState) (src dst : Buffer) (width count : ℕ) : Prop where
  zero : s.indices 0=0
  one : s.indices 1=1
  two : s.indices 2=2
  width : s.indices 18=width
  count : s.indices 26=count
  sourceRow : s.indices 27=src.coordinates
  sourceValue : s.indices 28=src.coefficients
  targetRow : s.indices 29=dst.coordinates
  targetValue : s.indices 30=dst.coefficients

structure Invariant (s : RAMState) (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry)) : Prop where
  config : Config s src dst width runs.flatten.length
  safeSource : src.Safe
  safeTarget : dst.Safe
  records : Records src s runs.flatten
  separated : Separated src runs.flatten.length dst runs.flatten.length

@[simp] theorem invariant_ofState (s : RAMState) (src dst : Buffer) (w : ℕ)
    (runs : List (List SparseEntry)) :
    Invariant (Store.ofState s).val src dst w runs ↔Invariant s src dst w runs := by
  constructor <;> intro h
  · refine ⟨?_,h.safeSource,h.safeTarget,(Merge.records_ofState _ _ _).mp h.records,h.separated⟩
    exact ⟨h.config.zero,h.config.one,h.config.two,h.config.width,h.config.count,h.config.sourceRow,
      h.config.sourceValue,h.config.targetRow,h.config.targetValue⟩
  · refine ⟨?_,h.safeSource,h.safeTarget,(Merge.records_ofState _ _ _).mpr h.records,h.separated⟩
    exact ⟨h.config.zero,h.config.one,h.config.two,h.config.width,h.config.count,h.config.sourceRow,
      h.config.sourceValue,h.config.targetRow,h.config.targetValue⟩

/-- Across sorting passes, only the two data buffers may change. -/
def Frame (src dst : Buffer) (n : ℕ) (s t : RAMState) : Prop :=
  (∀j,100≤j → (j<src.coordinates ∨src.coordinates+2*n≤j) →
    (j<dst.coordinates ∨dst.coordinates+2*n≤j) →t.indices j=s.indices j) ∧
  (∀j,1≤j → (j<src.coefficients ∨src.coefficients+n≤j) →
    (j<dst.coefficients ∨dst.coefficients+n≤j) →t.words j=s.words j)

theorem Frame.refl (src dst : Buffer) (n : ℕ) (s : RAMState) : Frame src dst n s s :=
  ⟨fun _ _ _ _=>rfl,fun _ _ _ _=>rfl⟩

theorem Frame.symm {src dst : Buffer} {n : ℕ} {s t : RAMState} (h : Frame src dst n s t) :
    Frame dst src n s t := ⟨fun j hj ha hb=>h.1 j hj hb ha,fun j hj ha hb=>h.2 j hj hb ha⟩

theorem Frame.trans {src dst : Buffer} {n : ℕ} {s t u : RAMState}
    (h : Frame src dst n s t) (k : Frame src dst n t u) : Frame src dst n s u :=
  ⟨fun j hj ha hb=>(k.1 j hj ha hb).trans (h.1 j hj ha hb),
    fun j hj ha hb=>(k.2 j hj ha hb).trans (h.2 j hj ha hb)⟩

theorem frame_of_dataFrame {src dst : Buffer} {n : ℕ} {s t : RAMState}
    (h : DataFrame dst n s t) : Frame src dst n s t :=
  ⟨fun j hj _ hb=>h.1 j hj hb,fun j hj _ hb=>h.2 j hj hb⟩

theorem Invariant.prepared {s : RAMState} {src dst : Buffer} {w : ℕ} {runs : List (List SparseEntry)}
    (h : Invariant s src dst w runs) : Pass.Invariant (OuterControl.prepared s) src dst w runs.flatten := by
  refine ⟨?_,h.safeSource,h.safeTarget,
    h.records.dataFrame_zero h.safeSource (OuterControl.prepare_data_frame s dst),h.separated⟩
  constructor <;> simp [OuterControl.prepared,RAMState.setIndex,
    h.config.zero,h.config.one,h.config.two,h.config.count,h.config.width,
    h.config.sourceRow,h.config.sourceValue,h.config.targetRow,h.config.targetValue]

theorem Config.advanced {s : RAMState} {src dst : Buffer} {w n : ℕ}
    (h : Config s src dst w n) : Config (OuterControl.advanced s) dst src (2*w) n := by
  constructor <;> simp [OuterControl.advanced,RAMState.setIndex,
    h.zero,h.one,h.two,h.count,h.width,h.sourceRow,h.sourceValue,h.targetRow,h.targetValue,two_mul]

def bufferAfter : ℕ→Buffer→Buffer→Buffer
  | 0,src,_=>src
  | k+1,src,dst=>bufferAfter k dst src

end Maxwell.Cost.RealSparseOrder.Sort
