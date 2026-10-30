import Maxwell.Continuum.SourceRoutingPortPrivate
import Maxwell.Continuum.SourceRoutingPairWrite

/-! The common preservation relation for routing arithmetic and indexed
memory access. Persistent source tapes and I/O survive either operation. -/

namespace Maxwell.Cost.RoutingPorts.Complete

structure ArchiveFrame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,(i=4 ∨ 10 ≤ i)→i∉work→t.tapes i=s.tapes i

theorem ArchiveFrame.refl (work : Finset ℕ) (s : BitRAMState) : ArchiveFrame work s s :=
  ⟨rfl,rfl,rfl,fun _ _ _ => rfl⟩
theorem ArchiveFrame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : ArchiveFrame work s t) (k : ArchiveFrame work t u) : ArchiveFrame work s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hn => (k.tapes i hi hn).trans (h.tapes i hi hn)⟩
theorem ArchiveFrame.mono {work larger : Finset ℕ} {s t : BitRAMState}
    (h : ArchiveFrame work s t) (hle : work⊆larger) : ArchiveFrame larger s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi hn => h.tapes i hi (fun hm => hn (hle hm))⟩
theorem ArchiveFrame.of_binary {work : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame work s t) : ArchiveFrame work s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i _ hi => h.tapes i hi⟩
theorem ArchiveFrame.of_complete {work : Finset ℕ} {s t : BitRAMState}
    (h : Frame work s t) : ArchiveFrame work s t :=
  ⟨h.inputHead,h.randomCursor,h.output,h.tapes⟩
theorem ArchiveFrame.of_bank {bank : ℕ} {s t : BitRAMState}
    (h : BankArray.FrameExcept bank s t) : ArchiveFrame {bank} s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hn => h.2.2.2.1 i hi (by simpa using hn)⟩

theorem Metadata.archive {n : ℕ} {l : Layout n} {s t : BitRAMState}
    (h : Metadata l s) {work : Finset ℕ} (hf : ArchiveFrame work s t)
    (hwork : ∀i∈work,i≠709 ∧ i≠711 ∧ i≠716 ∧ i≠717 ∧ i≠718) : Metadata l t := by
  have keep (i : ℕ) (hi : i=709 ∨ i=711 ∨ i=716 ∨ i=717 ∨ i=718) : t.tapes i=s.tapes i :=
    hf.tapes i (Or.inr (by omega)) (by intro hh; have := hwork i hh; omega)
  exact ⟨RationalAccumulator.word_of_eq (keep 709 (by decide)) h.count,
    RationalAccumulator.word_of_eq (keep 711 (by decide)) h.width,
    RationalAccumulator.word_of_eq (keep 716 (by decide)) h.forward,
    RationalAccumulator.word_of_eq (keep 717 (by decide)) h.backward,
    BankArray.word_of_eq (keep 718 (by decide)) h.clock⟩

#print axioms Metadata.archive

end Maxwell.Cost.RoutingPorts.Complete
