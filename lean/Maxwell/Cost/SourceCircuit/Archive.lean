import Maxwell.Cost.TapeLog
import Maxwell.Cost.WordCall
import Maxwell.Cost.BankArray.Common

/-! Finite tape-to-archive transfers used by the circuit compiler. A parent
identifier is copied from its actual binary bank, then the bank is rewound.
Only the tag is a compile-time literal. -/

namespace Maxwell.Cost.SourceCircuit
open Structured

def appendCode (source archive : ℕ) : Code :=
  .seq (.call (TapeLog.program source archive false)) (.call (Rewind.program source))

theorem append_executes (source archive : ℕ) (hne : source ≠ archive)
    (input : List Bool) (randomTape : ℕ → Bool) (word preceding : List Bool)
    (origin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted word origin)
    (ha : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape (appendCode source archive) (11 * word.length + 10) s t ∧
      t.val.tapes = Function.update s.val.tapes archive (BitTape.atEnd (preceding ++ word)) ∧
      WordTransfer.Frame source archive s.val t.val := by
  have represents : (s.val.tapes source).Represents word := by
    intro k
    simp [hs, BitTape.shifted]
  have hp := TapeLog.steps source archive hne false input randomTape word preceding
    s.val s.property represents ha (by simp)
  let p := Store.ofState (TapeLog.finish source archive false word preceding s.val)
  have ep : Executes input randomTape (.call (TapeLog.program source archive false))
      (7 * word.length + 4) s p := .call _ s _ _ hp rfl
  have hw : p.val.tapes source = BitTape.shiftedEnd word origin := by
    simp [p, Store.ofState, TapeLog.finish_source, hne, hs, BitTape.shiftedEnd, BitTape.shifted]
  have hr := WordTransfer.rewind_shifted source origin input randomTape word p.val p.property hw
  let t := Store.ofState (Rewind.finishAt source origin p.val)
  have er : Executes input randomTape (.call (Rewind.program source))
      (4 * word.length + 6) p t := .call _ p _ _ hr.1 rfl
  have frame := (WordTransfer.frame_of_copy
    (TapeLog.finish_frame source archive false word preceding s.val)).trans
    (WordTransfer.frame_rewind source archive source (Or.inl rfl) origin p.val)
  refine ⟨t, ?_, ?_, frame⟩
  · convert ep.seq er using 1 <;> first | rfl | omega
  · funext j
    by_cases hja : j = archive
    · subst j
      simp [t, Store.ofState, Rewind.finishAt, Ne.symm hne, p, TapeLog.finish_target,
        show TapeLog.symbol false = (fun b => b) from rfl]
    · by_cases hjs : j = source
      · subst j
        simpa [t, Store.ofState, hja, hs] using hr.2
      · simpa [t, Store.ofState, hja] using frame.2.2.2.2.2.1 j hjs hja

def appendBitCode (archive register : ℕ) : Code :=
  .seq (.atom (.writeTape archive register)) (.atom (.tapeRight archive))

theorem appendBit_executes (archive register : ℕ) (input : List Bool)
    (randomTape : ℕ → Bool) (preceding : List Bool) (s : Store)
    (ha : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape (appendBitCode archive register) 4 s t ∧
      t.val.tapes = Function.update s.val.tapes archive
        (BitTape.atEnd (preceding ++ [s.val.registers register])) ∧
      t.val.registers = s.val.registers ∧ WordTransfer.Frame archive archive s.val t.val := by
  let w := Store.ofState (s.val.setTape archive
    ((s.val.tapes archive).write (some (s.val.registers register))))
  let t := Store.ofState (w.val.setTape archive
    {w.val.tapes archive with head := (w.val.tapes archive).head + 1})
  refine ⟨t, (Executes.writeTape input randomTape s archive register).seq
    (Executes.tapeRight input randomTape w archive), ?_, rfl, ?_⟩
  · have hh := BitTape.append_write preceding (s.val.registers register)
    simpa [t, w, Store.ofState, BitRAMState.setTape, BitTape.write, ha] using
      congrArg (Function.update s.val.tapes archive) hh
  · simp [WordTransfer.Frame, t, w, Store.ofState, BitRAMState.setTape]
    intros
    simp_all

def tagCode (archive : ℕ) : List Bool → Code
  | [] => .skip
  | b :: rest => .seq (.atom (.literal 26 b))
      (.seq (appendBitCode archive 26) (tagCode archive rest))

theorem tag_executes (archive : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (tag preceding : List Bool) (s : Store)
    (ha : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape (tagCode archive tag) (6 * tag.length + 1) s t ∧
      t.val.tapes = Function.update s.val.tapes archive (BitTape.atEnd (preceding ++ tag)) ∧
      WordTransfer.Frame archive archive s.val t.val := by
  induction tag generalizing preceding s with
  | nil =>
    refine ⟨s, .skip s, ?_, ?_⟩
    · simp [← ha]
    · simp [WordTransfer.Frame]
  | cons b rest ih =>
    let l := Store.ofState (s.val.setRegister 26 b)
    have el := Executes.literal input randomTape s 26 b
    obtain ⟨w,ew,hw,_,wf⟩ := appendBit_executes archive 26 input randomTape preceding l ha
    have hwa : w.val.tapes archive = BitTape.atEnd (preceding ++ [b]) := by
      simp [hw, l, Store.ofState, BitRAMState.setRegister]
    obtain ⟨t,et,ht,tf⟩ := ih (preceding ++ [b]) w hwa
    have lf : WordTransfer.Frame archive archive s.val l.val := by
      simp [WordTransfer.Frame, l, Store.ofState, BitRAMState.setRegister]
      intros
      simp_all
    refine ⟨t, ?_, ?_, lf.trans (wf.trans tf)⟩
    · convert el.seq (ew.seq et) using 1 <;> first | rfl | simp; omega
    · simp [ht, hw, l, Store.ofState, BitRAMState.setRegister, List.append_assoc]

def gateCode (parent archive : ℕ) (tag : List Bool) : Code :=
  .seq (tagCode archive tag) (appendCode parent archive)

/-- One fixed-tag gate record, read from an actual parent bank. -/
theorem gate_executes (parent archive : ℕ) (hne : parent ≠ archive)
    (input : List Bool) (randomTape : ℕ → Bool) (tag word preceding : List Bool)
    (origin : ℤ) (s : Store)
    (hp : s.val.tapes parent = BitTape.shifted word origin)
    (ha : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape (gateCode parent archive tag)
        (6 * tag.length + 11 * word.length + 11) s t ∧
      t.val.tapes = Function.update s.val.tapes archive
        (BitTape.atEnd (preceding ++ tag ++ word)) ∧
      WordTransfer.Frame parent archive s.val t.val := by
  obtain ⟨u,eu,hu,uf⟩ := tag_executes archive input randomTape tag preceding s ha
  obtain ⟨t,et,ht,tf⟩ := append_executes parent archive hne input randomTape word
    (preceding ++ tag) origin u (by simpa [hu, hne] using hp) (by simp [hu])
  have uf' : WordTransfer.Frame parent archive s.val u.val :=
    ⟨uf.1,uf.2.1,uf.2.2.1,uf.2.2.2.1,uf.2.2.2.2.1,
      fun j _ hja => uf.2.2.2.2.2.1 j hja hja,uf.2.2.2.2.2.2⟩
  refine ⟨t, ?_, ?_, uf'.trans tf⟩
  · convert eu.seq et using 1 <;> first | rfl | omega
  · simp [ht,hu]

end Maxwell.Cost.SourceCircuit
