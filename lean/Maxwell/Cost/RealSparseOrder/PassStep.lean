import Maxwell.Cost.RealSparseOrder.PassBlock
import Maxwell.Cost.RealSparseOrder.PassSetup

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control

def stepCode : Code := .seq (.call PassSetup.program) blockCode

def loopCode : Code := .loop 1 17 stepCode

theorem Config.setupReady {s : RAMState} {src dst : Buffer} {w n : ℕ}
    (h : Config s src dst w n) : PassSetup.Ready s src dst w n :=
  ⟨h.zero,h.one,h.two,h.remaining,h.width,h.sourceRow,h.sourceValue,h.targetRow,h.targetValue⟩

theorem Config.after_setup {s : RAMState} {src dst : Buffer} {w n : ℕ}
    (h : Config s src dst w n) : Config (PassSetup.initialized s) src dst w n := by
  have hr := PassSetup.ready_preserved h.setupReady
  exact ⟨hr.zero,hr.one,hr.two,hr.remaining,hr.width,hr.sourceRow,hr.sourceValue,hr.targetRow,hr.targetValue⟩

theorem Invariant.after_setup {s : RAMState} {src dst : Buffer} {w : ℕ} {es : List SparseEntry}
    (h : Invariant s src dst w es) : Invariant (PassSetup.initialized s) src dst w es :=
  ⟨h.config.after_setup,h.safeSource,h.safeTarget,
    h.records.dataFrame_zero h.safeSource (PassSetup.data_frame s dst),h.separated⟩

/-- A complete physical pass iteration: finite boundary arithmetic, the
addressed merge, and finite descriptor advancement. -/
theorem step (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (width : ℕ) (xs ys rest : List SparseEntry)
    (h : Invariant s.val src dst width (xs++ys++rest))
    (hl : xs.length=min width (xs++ys++rest).length)
    (hr : ys.length=min width ((xs++ys++rest).length-xs.length)) :
    ∃cost t, cost≤28*(xs.length+ys.length)+25 ∧
      Executes input tape stepCode cost s t ∧
      Invariant t.val (src.shift (xs.length+ys.length))
        (dst.shift (xs.length+ys.length)) width rest ∧
      Records dst t.val (merge xs ys) ∧
      DataFrame dst (xs.length+ys.length) s.val t.val ∧
      ControlFrame s.val t.val ∧Merge.Channels s.val t.val := by
  let mid := Store.ofState (PassSetup.initialized s.val)
  have hm : Invariant mid.val src dst width (xs++ys++rest) :=
    (invariant_ofState _ _ _ _ _).mpr h.after_setup
  have cfg : Merge.Config mid.val src xs.length (src.shift xs.length) ys.length dst := by
    apply (Merge.config_ofState _ _ _ _ _ _).mpr
    simpa only [← hl,← hr] using PassSetup.configuration h.config.setupReady
  have hc : mid.val.indices 24=xs.length+ys.length := by
    change (PassSetup.initialized s.val).indices 24=_
    simpa only [← hl,← hr] using (PassSetup.saved_sizes h.config.setupReady).1
  have hc2 : mid.val.indices 25=2*(xs.length+ys.length) := by
    change (PassSetup.initialized s.val).indices 25=_
    simpa only [← hl,← hr] using (PassSetup.saved_sizes h.config.setupReady).2
  obtain ⟨cost,t,hcost,run,hi,records,frame,control,channels⟩ :=
    block input tape mid src dst width xs ys rest hm cfg hc hc2
  refine ⟨18+cost,t,by omega,Executes.seq (PassSetup.executes input tape s) run,
    hi,records,?_,?_,channels⟩
  · exact ((PassSetup.data_frame s.val dst).mono (by omega)).trans frame
  · intro j hj hk
    exact (control j hj hk).trans (PassSetup.indices_frame s.val j (Or.inr (Or.inr hj)))

end Maxwell.Cost.RealSparseOrder.Pass
