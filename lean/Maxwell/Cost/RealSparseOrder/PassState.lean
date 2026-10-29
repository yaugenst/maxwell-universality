import Maxwell.Cost.RealSparseOrder.DataFrame
import Maxwell.Cost.RealSparseOrder.Records
import Maxwell.Cost.RealSparseOrder.PassAdvance
import Maxwell.Cost.RealSparseOrder.MergeLoop

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control

structure Config (s : RAMState) (src dst : Buffer) (width remaining : ℕ) : Prop where
  zero : s.indices 0=0
  one : s.indices 1=1
  two : s.indices 2=2
  remaining : s.indices 17=remaining
  width : s.indices 18=width
  sourceRow : s.indices 19=src.coordinates
  sourceValue : s.indices 20=src.coefficients
  targetRow : s.indices 21=dst.coordinates
  targetValue : s.indices 22=dst.coefficients

@[simp] theorem config_ofState (s : RAMState) (src dst : Buffer) (width remaining : ℕ) :
    Config (Store.ofState s).val src dst width remaining ↔Config s src dst width remaining := by
  constructor <;> intro h <;> exact ⟨h.zero,h.one,h.two,h.remaining,h.width,
    h.sourceRow,h.sourceValue,h.targetRow,h.targetValue⟩

structure Invariant (s : RAMState) (src dst : Buffer) (width : ℕ) (es : List SparseEntry) : Prop where
  config : Config s src dst width es.length
  safeSource : src.Safe
  safeTarget : dst.Safe
  records : Records src s es
  separated : Separated src es.length dst es.length

@[simp] theorem invariant_ofState (s : RAMState) (src dst : Buffer) (width : ℕ) (es : List SparseEntry) :
    Invariant (Store.ofState s).val src dst width es ↔Invariant s src dst width es := by
  constructor <;> intro h
  · exact ⟨(config_ofState _ _ _ _ _).mp h.config,h.safeSource,h.safeTarget,
      (Merge.records_ofState _ _ _).mp h.records,h.separated⟩
  · exact ⟨(config_ofState _ _ _ _ _).mpr h.config,h.safeSource,h.safeTarget,
      (Merge.records_ofState _ _ _).mpr h.records,h.separated⟩

theorem Config.advance {s : RAMState} {src dst : Buffer} {w n count : ℕ}
    (h : Config s src dst w n) (hc : s.indices 24=count) (hc2 : s.indices 25=2*count) :
    Config (PassAdvance.advanced s) (src.shift count) (dst.shift count) w (n-count) := by
  constructor <;> simp [PassAdvance.advanced,RAMState.setIndex,Buffer.shift,
    h.zero,h.one,h.two,h.remaining,h.width,h.sourceRow,h.sourceValue,h.targetRow,h.targetValue,hc,hc2]

/-- The merge writes only data; all pass descriptors remain unchanged. -/
theorem Config.after_merge {s t : RAMState} {src dst : Buffer} {w n count : ℕ}
    (h : Config s src dst w n) (hd : dst.Safe)
    (hf : MemoryFrame dst count s t)
    (hz : t.indices 0=0) (ho : t.indices 1=1) (ht : t.indices 2=2) :
    Config t src dst w n := by
  have hsmall (j : ℕ) (hlo : 17≤j) (hhi : j<100) : t.indices j=s.indices j :=
    hf.1 j hlo (Or.inl (by have hh := hd.2; omega))
  exact ⟨hz,ho,ht,(hsmall 17 (by omega) (by omega)).trans h.remaining,
    (hsmall 18 (by omega) (by omega)).trans h.width,
    (hsmall 19 (by omega) (by omega)).trans h.sourceRow,
    (hsmall 20 (by omega) (by omega)).trans h.sourceValue,
    (hsmall 21 (by omega) (by omega)).trans h.targetRow,
    (hsmall 22 (by omega) (by omega)).trans h.targetValue⟩

theorem records_advance {s : RAMState} {src : Buffer} {es : List SparseEntry}
    (h : Records src s es) (hs : src.Safe) : Records src (PassAdvance.advanced s) es :=
  h.dataFrame_zero hs (PassAdvance.data_frame s src)

end Maxwell.Cost.RealSparseOrder.Pass
