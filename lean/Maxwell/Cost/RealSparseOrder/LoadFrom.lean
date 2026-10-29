import Maxwell.Cost.RealSparseOrder.BoundedLoad
import Maxwell.Cost.RealSparseOrder.LoadFrame

namespace Maxwell.Cost.RealSparseOrder.Load
open RealSimulation.Control

theorem initializedFrom_frame (s : RAMState) (m : ℕ) : Frame m s (initializedFrom s m) := by
  constructor
  · intro j hj _
    simp [initializedFrom,RAMState.setIndex,show j≠0 by omega,show j≠1 by omega,
      show j≠2 by omega,show j≠3 by omega,show j≠4 by omega,show j≠5 by omega,
      show j≠6 by omega,show j≠9 by omega]
  · intro _ _ _; rfl

/-- The unchanged literal loader is callable after earlier work. In
particular an already computed transpose product in a disjoint buffer is
retained by actual machine execution. -/
theorem from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool) (s : Store) :
    ∃t : Store,Executes (RealSparse.input es vector) tape (.call program) (14*es.length+10) s t ∧
      Stored initialBuffer t.val es ∧Frame es.length s.val t.val ∧
      t.val.randomCursor=s.val.randomCursor ∧t.val.output=s.val.output ∧t.val.indexOutput=s.val.indexOutput := by
  let start := initializedFrom s.val es.length
  have ready : Ready start es.length 0 := initializedFrom_ready s.val _ s.property
  obtain ⟨t,run,hpc,stored,random,output,indexOutput⟩ := loop es vector tape es.length 0 start
    ready (by omega) (by intro j hj; omega)
  obtain ⟨u,frun,_,frame⟩ := loop_frame es vector tape es.length 0 start ready (by omega)
  have same : t=u := Option.some.inj
    ((runCapped_of_terminates _ run).1.symm.trans (runCapped_of_terminates _ frun).1)
  subst u
  have actual : Terminates (program.next (RealSparse.input es vector) tape) (14*es.length+9) s.val t := by
    convert (RealSparse.execute_sound _ (initialize_steps_from es vector tape s.val s.property)).terminates run using 1
    omega
  refine ⟨Store.ofState t,?_,stored,(initializedFrom_frame s.val es.length).trans frame,random,output,indexOutput⟩
  convert Executes.call program s t (14*es.length+9) actual.toSteps (by simp [program,hpc]) using 1

end Maxwell.Cost.RealSparseOrder.Load
