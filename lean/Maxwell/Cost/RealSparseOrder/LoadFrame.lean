import Maxwell.Cost.RealSparseOrder.Load

namespace Maxwell.Cost.RealSparseOrder.Load

/-- Loader frame retains earlier work outside its actual COO destinations. -/
def Frame (m : ℕ) (s t : RAMState) : Prop :=
  (∀j,10≤j → (j<100 ∨100+2*m≤j) → t.indices j=s.indices j) ∧
  (∀j,1≤j → (j<100 ∨100+m≤j) → t.words j=s.words j)

theorem Frame.refl (m : ℕ) (s : RAMState) : Frame m s s := ⟨by intros; rfl,by intros; rfl⟩

theorem Frame.trans {m : ℕ} {s t u : RAMState} (h : Frame m s t) (g : Frame m t u) : Frame m s u :=
  ⟨fun j hj hout=>(g.1 j hj hout).trans (h.1 j hj hout),
    fun j hj hout=>(g.2 j hj hout).trans (h.2 j hj hout)⟩

theorem advanced_frame (s : RAMState) (m k : ℕ) (h : Ready s m k)
    (hk : k<m) (e : SparseEntry) : Frame m s (advanced s e) := by
  rcases h with ⟨_,_,_,_,_,_,_,hc,hv⟩
  constructor
  · intro j hj hout
    have hrow : j≠s.indices 6 := by rw [hc]; omega
    have hcol : j≠s.indices 6+1 := by rw [hc]; omega
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hrow,hcol,
      show j≠4 by omega,show j≠5 by omega,show j≠6 by omega,
      show j≠7 by omega,show j≠8 by omega,show j≠9 by omega]
  · intro j hj hout
    have hvalue : j≠s.indices 9 := by rw [hv]; omega
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hvalue,show j≠0 by omega]

/-- The direct loader trace retains the full frame after every consumed
record, including runs starting after earlier preprocessing. -/
theorem loop_frame (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (remaining k : ℕ) (s : RAMState) (hr : Ready s es.length k)
    (hc : k+remaining=es.length) :
    ∃t,Terminates (program.next (RealSparse.input es vector) tape) (14*remaining+1) s t ∧
      t.pc=22 ∧Frame es.length s t := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k=es.length := by omega
    subst k
    let t : RAMState := {s with pc:=22}
    have step : program.next (RealSparse.input es vector) tape s=some t := by
      simp [Machine.next,program,hr.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,t]
    refine ⟨t,Terminates.step step (Terminates.halt t ?_),rfl,Frame.refl _ _⟩
    simp [program,Machine.next,t]
  | succ remaining ih =>
    have hk : k<es.length := by omega
    obtain ⟨t,run,hpc,frame⟩ := ih (k+1) (advanced s (RealSparse.entryAt es k))
      (advanced_ready s _ k hr _) (by omega)
    refine ⟨t,?_,hpc,(advanced_frame s _ k hr hk _).trans frame⟩
    convert (RealSparse.execute_sound _ (cycle es vector tape s k hr hk)).terminates run using 1
    omega

end Maxwell.Cost.RealSparseOrder.Load
