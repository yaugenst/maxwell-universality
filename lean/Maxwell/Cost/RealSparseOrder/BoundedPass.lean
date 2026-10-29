import Maxwell.Cost.RealSparseOrder.BoundedMergeLoop
import Maxwell.Cost.RealSparseOrder.PassIndexBounds
import Maxwell.Cost.RealSparseOrder.PassStep

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control RealSimulation.IndexWidth

/-- Every pass stage preserves a fixed cap on stored coordinates and array ends. -/
structure Bounded (B : ℕ) (s : RAMState) (src dst : Buffer) (width : ℕ)
    (es : List SparseEntry) : Prop where
  invariant : Invariant s src dst width es
  indices : IndexBound B s
  sourceEnd : Within B src es.length
  targetEnd : Within B dst es.length
  size : 2*es.length≤B

@[simp] theorem bounded_ofState (B : ℕ) (s : RAMState) (src dst : Buffer) (width : ℕ)
    (es : List SparseEntry) :
    Bounded B (Store.ofState s).val src dst width es ↔Bounded B s src dst width es := by
  constructor <;> intro h
  · exact ⟨(invariant_ofState _ _ _ _ _).mp h.invariant,h.indices,h.sourceEnd,h.targetEnd,h.size⟩
  · exact ⟨(invariant_ofState _ _ _ _ _).mpr h.invariant,h.indices,h.sourceEnd,h.targetEnd,h.size⟩

theorem Bounded.after_setup {B : ℕ} {s : RAMState} {src dst : Buffer} {width : ℕ}
    {es : List SparseEntry} (h : Bounded B s src dst width es) :
    Bounded B (PassSetup.initialized s) src dst width es :=
  ⟨h.invariant.after_setup,passSetup_index_bound h.invariant.config h.indices h.sourceEnd h.size,
    h.sourceEnd,h.targetEnd,h.size⟩

theorem bounded_block (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (xs ys rest : List SparseEntry)
    (h : Bounded B s.val src dst width (xs++ys++rest))
    (cfg : Merge.Config s.val src xs.length (src.shift xs.length) ys.length dst)
    (hc : s.val.indices 24=xs.length+ys.length)
    (hc2 : s.val.indices 25=2*(xs.length+ys.length)) :
    ∃cost t, BoundedExecutes B 30 input tape blockCode cost s t := by
  have hi := h.invariant
  have hsrc : Records src s.val (xs++(ys++rest)) := by simpa only [List.append_assoc] using hi.records
  rcases (records_append src s.val xs (ys++rest)).mp hsrc with ⟨hxs,htail⟩
  rcases (records_append (src.shift xs.length) s.val ys rest).mp htail with ⟨hys,_⟩
  have mi : Merge.Invariant s.val src (src.shift xs.length) dst xs ys := by
    refine ⟨cfg,hi.safeSource,hi.safeSource.shift _,hi.safeTarget,hxs,hys,?_,?_⟩
    · simpa using hi.separated.subset (i:=0) (r:=xs.length) (j:=0) (q:=xs.length+ys.length)
        (by simp) (by simp)
    · simpa using hi.separated.subset (i:=xs.length) (r:=ys.length) (j:=0) (q:=xs.length+ys.length)
        (by simp) (by simp)
  have mb : Merge.Bounded B s.val src (src.shift xs.length) dst xs ys := by
    refine ⟨mi,h.indices,?_,h.sourceEnd.subset (by simp),?_⟩
    · simpa using h.sourceEnd.subset (i:=0) (n:=xs.length) (by simp)
    · simpa using h.targetEnd.subset (i:=0) (n:=xs.length+ys.length) (by simp)
  obtain ⟨cost,mid,af,bf,_,run,mcfg,_,frame,_⟩ :=
    Merge.executes input tape s src (src.shift xs.length) dst xs ys mi
  obtain ⟨other,u,bounded⟩ := Merge.bounded_loop input tape B s src (src.shift xs.length) dst xs ys mb
  obtain ⟨rfl,rfl⟩ := run.deterministic bounded.executes
  have hmeta (j : ℕ) (hlo : 17≤j) (hhi : j<100) : mid.val.indices j=s.val.indices j :=
    frame.1 j hlo (Or.inl (by have hh := hi.safeTarget.2; omega))
  have pcfg := hi.config.after_merge hi.safeTarget frame mcfg.zero mcfg.one mcfg.two
  have hc' : mid.val.indices 24=xs.length+ys.length := (hmeta 24 (by omega) (by omega)).trans hc
  have hc2' : mid.val.indices 25=2*(xs.length+ys.length) := (hmeta 25 (by omega) (by omega)).trans hc2
  have hfinish := passAdvance_index_bound pcfg bounded.finish h.sourceEnd h.targetEnd hc' hc2'
    (by simp)
  exact ⟨cost+6,Store.ofState (PassAdvance.advanced mid.val),
    BoundedExecutes.seq bounded (.atom (PassAdvance.executes input tape mid) (by omega)
      bounded.finish hfinish)⟩

theorem bounded_step (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (xs ys rest : List SparseEntry)
    (h : Bounded B s.val src dst width (xs++ys++rest))
    (hl : xs.length=min width (xs++ys++rest).length)
    (hr : ys.length=min width ((xs++ys++rest).length-xs.length)) :
    ∃cost t, BoundedExecutes B 30 input tape stepCode cost s t := by
  let mid := Store.ofState (PassSetup.initialized s.val)
  have hm : Bounded B mid.val src dst width (xs++ys++rest) :=
    (bounded_ofState _ _ _ _ _ _).mpr h.after_setup
  have cfg : Merge.Config mid.val src xs.length (src.shift xs.length) ys.length dst := by
    apply (Merge.config_ofState _ _ _ _ _ _).mpr
    simpa only [← hl,← hr] using PassSetup.configuration h.invariant.config.setupReady
  have hc : mid.val.indices 24=xs.length+ys.length := by
    change (PassSetup.initialized s.val).indices 24=_
    simpa only [← hl,← hr] using (PassSetup.saved_sizes h.invariant.config.setupReady).1
  have hc2 : mid.val.indices 25=2*(xs.length+ys.length) := by
    change (PassSetup.initialized s.val).indices 25=_
    simpa only [← hl,← hr] using (PassSetup.saved_sizes h.invariant.config.setupReady).2
  obtain ⟨cost,t,run⟩ := bounded_block input tape B mid src dst width xs ys rest hm cfg hc hc2
  exact ⟨18+cost,t,BoundedExecutes.seq
    (.atom (PassSetup.executes input tape s) (by omega) h.indices hm.indices) run⟩

end Maxwell.Cost.RealSparseOrder.Pass
