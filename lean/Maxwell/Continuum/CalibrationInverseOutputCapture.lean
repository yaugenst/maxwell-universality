import Maxwell.Continuum.CalibrationInverseOutputPoint
import Maxwell.Continuum.RationalDataflowStoredParts
import Maxwell.Cost.BankArray.ScratchFrame

/-! Capture a computed inverse entry in a retained raw rational register.
Only its three destination words are changed, so the same array readout and
its computed index bank can be reused for the next neighbor. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputPoint
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow
set_option maxHeartbeats 3000000

theorem State.capture_frame {n D target : ℕ} {a : Snapshot n} {v : ℕ→ℕ} {s t : BitRAMState}
    (h : State a D v s) (f : BinaryPrecision.Frame (cellPorts target) s t) : State a D v t := by
  have keep (k : ℕ) (hk:k<1000) : t.tapes k=s.tapes k := by
    apply f.tapes
    have hp:=positivePort_ge target
    have hn:=negativePort_ge target
    have hd:=denominatorPort_ge target
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨h.stored.of_memory_tapes f.memory ?_,?_,?_,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven,?_,
    RationalAccumulator.word_of_eq (keep 532 (by decide)) h.denominator⟩
  · intro k hk
    simp only [Horner.Metadata] at hk
    exact keep k (by omega)
  · exact ⟨BankArray.word_of_eq (keep 112 (by decide)) h.ports.inputPositive,
      BankArray.word_of_eq (keep 113 (by decide)) h.ports.inputNegative,
      BankArray.word_of_eq (keep 114 (by decide)) h.ports.outputPositive,
      BankArray.word_of_eq (keep 115 (by decide)) h.ports.outputNegative⟩
  · exact h.scratch.transfer (by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      exact keep k (by omega))
  · intro k hk
    simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton] at hk
    exact RationalAccumulator.word_of_eq (keep k (by omega)) (h.bank k (by
      simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton];exact hk))

theorem entry_stored {n D : ℕ} (a : Snapshot n) (i : Fin n) (v : ℕ→ℕ) (s : BitRAMState)
    (h : NatAssign.Bank OutputRead.ids (OutputRead.values a D i v) s) :
    StoredParts.Stored 30 (OutputRead.entryParts a D i) s := by
  exact ⟨by simpa only [OutputRead.values,Function.update_of_ne (by decide : (30:ℕ)≠32),
      Function.update_of_ne (by decide : (30:ℕ)≠31),Function.update_self] using h 30 (by decide),
    by simpa only [OutputRead.values,Function.update_of_ne (by decide : (31:ℕ)≠32),Function.update_self] using h 31 (by decide),
    by simpa only [OutputRead.values,Function.update_self,OutputRead.entryParts] using h 32 (by decide)⟩

theorem capture_executes {n D : ℕ} (a : Snapshot n) (v nv : ℕ→ℕ)
    (target : ℕ) (old x : Parts) (B : ℕ) (ho:old.Width B) (hx:x.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state:State a D v s.val) (indexBank:NatAssign.Bank OutputPrepare.indexIds nv s.val)
    (hold:StoredParts.Stored (positivePort target) old s.val) (source:StoredParts.Stored 30 x s.val) :
    ∃cost t, Executes input tape (StoredParts.restoreCode 30 target) cost s t ∧ cost≤63*(B+1) ∧
      State a D v t.val ∧ NatAssign.Bank OutputPrepare.indexIds nv t.val ∧
      StoredParts.Stored (positivePort target) x t.val ∧
      BinaryPrecision.Frame (cellPorts target) s.val t.val := by
  obtain ⟨cost,t,executes,bound,stored,_,frame⟩:=
    StoredParts.restore_words_executes 30 target (by decide) old x B ho hx input tape s hold source
  refine ⟨cost,t,executes,bound,state.capture_frame frame,?_,stored,frame⟩
  intro k hk
  have hp:=positivePort_ge target
  have hn:=negativePort_ge target
  have hd:=denominatorPort_ge target
  have bounds:k<1000:=by
    simp only [OutputPrepare.indexIds,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  exact RationalAccumulator.word_of_eq (frame.tapes k (by
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton];omega)) (indexBank k hk)

#print axioms capture_executes
end Maxwell.Continuum.Calibration.NeumannMachine.OutputPoint
