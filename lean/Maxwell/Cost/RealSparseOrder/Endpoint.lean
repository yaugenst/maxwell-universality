import Maxwell.Cost.RealSparseOrder.SortLoop
import Maxwell.Cost.RealSparseOrder.Initialize

namespace Maxwell.Cost.RealSparseOrder.Endpoint
open RealSimulation.Control

def code : Code := .seq (.call Load.program) (.seq (.call Initialize.program) Sort.loopCode)

def bound (m : ℕ) : ℕ := 108*m*m.size+16*m.size+14*m+22

def resultBuffer (m : ℕ) : Buffer := Sort.bufferAfter m.size initialBuffer (Initialize.secondaryBuffer m)
def spareBuffer (m : ℕ) : Buffer := Sort.bufferAfter m.size (Initialize.secondaryBuffer m) initialBuffer

/-- The same fixed finite program reads the original COO input, stores its
records, and sorts those addressed arrays. No output stream is reused as a
new input, and the coefficients move with their row-column keys. -/
theorem executes (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool) :
    ∃(cost : ℕ) (t : Store), cost≤bound es.length ∧
      Executes (RealSparse.input es vector) tape code cost (Store.ofState RAMState.initial) t ∧
      Sort.Config t.val (resultBuffer es.length) (spareBuffer es.length)
        (2^es.length.size) es.length ∧
      Records (resultBuffer es.length) t.val (bottomUpSort es) ∧
      t.val.randomCursor=0 ∧t.val.output=[] ∧t.val.indexOutput=[] := by
  obtain ⟨loaded,loadRun,stored,lr,lo,li⟩ := Load.executes es vector tape
  let start := Store.ofState (Initialize.initialized es.length loaded.val)
  have hi : Sort.Invariant start.val initialBuffer (Initialize.secondaryBuffer es.length) 1
      (singletonRuns es) := (Sort.invariant_ofState _ _ _ _ _).mpr (Initialize.invariant es loaded.val stored)
  obtain ⟨cost,t,hcost,run,inv,_,channels⟩ := Sort.executes (RealSparse.input es vector)
    tape start initialBuffer (Initialize.secondaryBuffer es.length) es hi
  refine ⟨(14*es.length+10)+(11+cost),t,?_,Executes.seq loadRun
    (Executes.seq (Initialize.executes es vector tape loaded) run),?_,inv.records,?_,?_,?_⟩
  · unfold bound
    omega
  · have hc := inv.config
    have hlen : (mergePasses es.length.size (singletonRuns es)).flatten.length=es.length :=
      bottomUpSort_length es
    simpa only [resultBuffer,spareBuffer,hlen] using hc
  · exact channels.1.trans lr
  · exact channels.2.1.trans lo
  · exact channels.2.2.trans li

/-- The operational endpoint exposes the sorted records in actual memory
under the program's runtime output descriptor. -/
theorem run (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool) :
    ∃(cost : ℕ) (t : Store), cost≤bound es.length ∧
      (runCapped (code.compile.next (RealSparse.input es vector) tape)
        (bound es.length+1) RAMState.initial).finished=some (t.place code.size) ∧
      (runCapped (code.compile.next (RealSparse.input es vector) tape)
        (bound es.length+1) RAMState.initial).instructions=cost ∧
      t.val.indices 27=(resultBuffer es.length).coordinates ∧
      t.val.indices 28=(resultBuffer es.length).coefficients ∧
      Records (resultBuffer es.length) t.val (bottomUpSort es) ∧
      (bottomUpSort es).Pairwise KeyLE ∧(bottomUpSort es).Perm es := by
  obtain ⟨cost,t,hcost,execution,cfg,records,_⟩ := executes es vector tape
  have hr := execution.compiled_run (bound es.length+1) (by omega)
  exact ⟨cost,t,hcost,hr.1,hr.2,cfg.sourceRow,cfg.sourceValue,records,
    bottomUpSort_sorted es,bottomUpSort_perm es⟩

end Maxwell.Cost.RealSparseOrder.Endpoint
