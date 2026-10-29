import Maxwell.Cost.RealSparseOrder.SortState

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control

def stepCode : Code := .seq (.call OuterControl.prepareProgram)
  (.seq Pass.loopCode (.call OuterControl.advanceProgram))

def loopCode : Code := .loop 18 26 stepCode

/-- One complete finite pass followed by a charged buffer swap and width doubling. -/
theorem step (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Invariant s.val src dst width runs) :
    ∃cost t, cost≤54*mergePassWork runs+15 ∧Executes input tape stepCode cost s t ∧
      Invariant t.val dst src (2*width) (mergePass runs) ∧
      Frame src dst runs.flatten.length s.val t.val ∧Merge.Channels s.val t.val := by
  let start := Store.ofState (OuterControl.prepared s.val)
  have hs : Pass.Invariant start.val src dst width runs.flatten :=
    (Pass.invariant_ofState _ _ _ _ _).mpr h.prepared
  obtain ⟨cost,mid,hcost,run,cfg,records,frame,control,channels⟩ :=
    Pass.executes input tape start src dst width runs hw hp hs
  have hm (j : ℕ) (hlo : 26≤j) (hhi : j<100) : mid.val.indices j=s.val.indices j :=
    (control j hlo hhi).trans (OuterControl.prepare_indices_frame s.val j (Or.inr (Or.inr (by omega))))
  have rootCfg : Config mid.val src dst width runs.flatten.length :=
    ⟨cfg.zero,cfg.one,cfg.two,cfg.width,(hm 26 (by omega) (by omega)).trans h.config.count,
      (hm 27 (by omega) (by omega)).trans h.config.sourceRow,
      (hm 28 (by omega) (by omega)).trans h.config.sourceValue,
      (hm 29 (by omega) (by omega)).trans h.config.targetRow,
      (hm 30 (by omega) (by omega)).trans h.config.targetValue⟩
  let t := Store.ofState (OuterControl.advanced mid.val)
  refine ⟨6+(cost+8),t,by omega,
    Executes.seq (OuterControl.prepare_executes input tape s)
      (Executes.seq run (OuterControl.advance_executes input tape mid)),?_,?_,channels⟩
  · apply (invariant_ofState _ _ _ _ _).mpr
    refine ⟨?_,h.safeTarget,h.safeSource,?_,?_⟩
    · simpa only [mergePass_mass] using rootCfg.advanced
    · exact records.dataFrame_zero h.safeTarget (OuterControl.advance_data_frame mid.val dst)
    · simpa only [mergePass_mass] using h.separated.symm
  · apply frame_of_dataFrame
    exact ((OuterControl.prepare_data_frame s.val dst).mono (by omega)).trans
      (frame.trans ((OuterControl.advance_data_frame mid.val dst).mono (by omega)))

end Maxwell.Cost.RealSparseOrder.Sort
