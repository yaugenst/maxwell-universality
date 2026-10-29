import Maxwell.Cost.BinarySplit.Metadata

namespace Maxwell.Cost.BinarySplit
open Structured

abbrev AdapterFrame := WordAssign.Frame conjugateAssignments

theorem AdapterFrame.keep {s t : BitRAMState} (h : AdapterFrame s t) (i : ℕ)
    (h82 : i≠82) (h84 : i≠84) (h85 : i≠85) (h86 : i≠86) : t.tapes i=s.tapes i :=
  h.2.2.2.2.2.1 i (by simp [conjugateAssignments,h82,h84,h85,h86])

theorem AdapterFrame.cycle {s t : BitRAMState} (h : AdapterFrame s t) : CycleSplit.Frame s t := by
  refine ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · intro i _ hp _ _
    apply h.keep i
    all_goals intro he; exact hp (by simp [DoublingPass.RoundPrivate,he])
  · intro i _ hi
    exact h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)

theorem AdapterFrame.workspace {s t : BitRAMState} (h : AdapterFrame s t)
    (work : DoublingInit.Workspace s) : DoublingInit.Workspace t :=
  DoublingInit.workspace_of_tapes (fun i hi => h.keep i
    (by rcases hi with hi | hi <;> simp_all [DoublingInit.Private,DoublingPass.Private] <;> omega)
    (by rcases hi with hi | hi <;> simp_all [DoublingInit.Private,DoublingPass.Private] <;> omega)
    (by rcases hi with hi | hi <;> simp_all [DoublingInit.Private,DoublingPass.Private] <;> omega)
    (by rcases hi with hi | hi <;> simp_all [DoublingInit.Private,DoublingPass.Private] <;> omega)) work

private theorem adapt (assignments : List WordAssign.Assignment)
    (hv : WordAssign.Valid metadataIds assignments)
    (targets : assignments.map Prod.snd=[82,84,85,86])
    (layout : Layout) (source target : DoublingPass.Layout) (clock : List Bool)
    (values : WordAssign.values assignments (metadata layout source clock)=metadata layout target clock)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (cfg : DoublingInit.Config ⟨source,layout.pairing,layout.conjugated⟩ [] clock s.val)
    (saved : Saved layout s.val) (work : DoublingInit.Workspace s.val) :
    ∃ t, Executes input tape (WordAssign.code assignments) (WordAssign.price assignments (metadata layout source clock)) s t ∧
      DoublingInit.Config ⟨target,layout.pairing,layout.conjugated⟩ [] clock t.val ∧
      Saved layout t.val ∧ DoublingInit.Workspace t.val ∧ AdapterFrame s.val t.val := by
  obtain ⟨t,he,bank,frame⟩ := WordAssign.executes assignments metadataIds input tape
    (metadata layout source clock) hv s (metadata_bank layout source clock s.val cfg saved)
  rw [values] at bank
  have fr : AdapterFrame s.val t.val := by
    simpa only [AdapterFrame,WordAssign.Frame,targets,conjugateAssignments,List.map_cons,List.map_nil] using frame
  exact ⟨t,he,metadata_config bank,metadata_saved bank,fr.workspace work,fr⟩

def conjugateCode : Code := WordAssign.code conjugateAssignments
def cycleCode : Code := WordAssign.code cycleAssignments

def conjugateCost (layout : Layout) (clock : List Bool) : ℕ :=
  WordAssign.price conjugateAssignments (metadata layout layout.half.route clock)

def cycleCost (layout : Layout) (clock : List Bool) : ℕ :=
  WordAssign.price cycleAssignments (metadata layout layout.conjugate clock)

theorem to_conjugate (layout : Layout) (clock : List Bool) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (cfg : DoublingInit.Config layout.half [] clock s.val)
    (saved : Saved layout s.val) (work : DoublingInit.Workspace s.val) :
    ∃ t, Executes input tape conjugateCode (conjugateCost layout clock) s t ∧
      DoublingInit.Config ⟨layout.conjugate,layout.pairing,layout.conjugated⟩ [] clock t.val ∧
      Saved layout t.val ∧ DoublingInit.Workspace t.val ∧ AdapterFrame s.val t.val :=
  adapt conjugateAssignments (by simp [WordAssign.Valid,conjugateAssignments,metadataIds]) rfl layout layout.half.route layout.conjugate clock
    (conjugate_metadata layout clock) input tape s cfg saved work

theorem to_cycle (layout : Layout) (clock : List Bool) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (cfg : DoublingInit.Config ⟨layout.conjugate,layout.pairing,layout.conjugated⟩ [] clock s.val)
    (saved : Saved layout s.val) (work : DoublingInit.Workspace s.val) :
    ∃ t, Executes input tape cycleCode (cycleCost layout clock) s t ∧
      DoublingInit.Config layout.cycle [] clock t.val ∧ Saved layout t.val ∧
      DoublingInit.Workspace t.val ∧ AdapterFrame s.val t.val :=
  adapt cycleAssignments (by simp [WordAssign.Valid,cycleAssignments,metadataIds]) rfl layout layout.conjugate layout.route clock
    (cycle_metadata layout clock) input tape s cfg saved work

end Maxwell.Cost.BinarySplit
