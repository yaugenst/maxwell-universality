import Maxwell.Cost.Structured.Syntax
import Maxwell.Cost.ParseEntry
import Maxwell.Cost.Copy
import Maxwell.Cost.LogNat
import Maxwell.Cost.ScanForward

namespace Maxwell.Cost.DecoderParser

open Structured

/-- The parser preserves all state outside its literal work tapes. -/
structure Frame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i ∉ work, t.tapes i = s.tapes i

theorem Frame.refl (work : Finset ℕ) (s : BitRAMState) : Frame work s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : Frame work s t) (k : Frame work t u) : Frame work s u :=
  ⟨k.address.trans h.address, k.memory.trans h.memory,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState}
    (h : Frame a s t) (hab : a ⊆ b) : Frame b s t :=
  ⟨h.address, h.memory, h.randomCursor, h.output,
    fun i hi => h.tapes i (fun ha => hi (hab ha))⟩

@[simp] theorem Frame.ofState {work : Finset ℕ} {s t : BitRAMState} :
    Frame work (Store.ofState s).val (Store.ofState t).val ↔ Frame work s t := by
  constructor <;> intro h <;>
    exact ⟨h.address, h.memory, h.randomCursor, h.output, h.tapes⟩

/-- Restore the unary parser counter using an actual head movement. -/
def resetCounter : BitRAM := ⟨[.tapeRight 10, .halt]⟩

def resetCounterState (s : BitRAMState) : BitRAMState :=
  {s with pc := 1, tapes := Function.update s.tapes 10 BitTape.blank}

theorem resetCounter_steps (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hs : s.val.tapes 10 = BitTape.beforeEnd []) :
    Executes input randomTape (.call resetCounter) 2 s (Store.ofState (resetCounterState s.val)) := by
  apply Executes.call resetCounter s (resetCounterState s.val) 1
  · apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, resetCounter, s.property, resetCounterState,
      BitRAMState.setTape, hs, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]
  · rfl

/-- Move to the end and erase a complete stored word. Both traversals are charged. -/
def clearWord (workTape : ℕ) : Code :=
  .seq (.call (ScanForward.program workTape)) (.call (TapeReset.program workTape))

theorem clearWord_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : Store) (hword : s.val.tapes workTape = BitTape.ofList bits) :
    ∃ t : Store, Executes input randomTape (clearWord workTape) (11 * bits.length + 10) s t ∧
      t.val.tapes workTape = BitTape.blank ∧ t.val.inputHead = s.val.inputHead ∧
      Frame {workTape} s.val t.val := by
  let f := ScanForward.finish workTape bits.length s.val
  have hs := ScanForward.steps workTape input randomTape bits s.val s.property
    (by rw [hword]; exact BitTape.ofList_represents bits)
  have hfword : f.tapes workTape = BitTape.atEnd bits := by
    simp [f, ScanForward.finish, hword, BitTape.atEnd, BitTape.ofList]
  let f' := Store.ofState f
  have ht := TapeReset.steps workTape input randomTape bits f'.val rfl hfword
  refine ⟨Store.ofState (TapeReset.finish workTape f'.val), ?_, by simp [TapeReset.finish,
    Store.ofState], rfl, ?_⟩
  · have h1 := Executes.call (ScanForward.program workTape) s f _ hs
      (by simp [f, ScanForward.finish, ScanForward.program])
    have h2 := Executes.call (TapeReset.program workTape) f'
      (TapeReset.finish workTape f'.val) _ ht (by simp [TapeReset.finish, TapeReset.program])
    convert h1.seq h2 using 1 <;> first | rfl | omega
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [Store.ofState, f', f, ScanForward.finish, TapeReset.finish, hi]

/-- Read and retain one raw bit, used for signs and fixed-width messages. -/
def readBit (archive : ℕ) : BitRAM := ⟨[
  .readSequential 23, .writeTape archive 23, .tapeRight archive, .inputRight, .halt]⟩

def readBitFinish (archive : ℕ) (b : Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 4
    inputHead := s.inputHead + 1
    registers := Function.update s.registers 23 b
    tapes := Function.update s.tapes archive
      {(s.tapes archive).write (some b) with head := (s.tapes archive).head + 1}}

theorem readBit_steps (archive : ℕ) (b : Bool) (preceding suffix saved : List Bool)
    (randomTape : ℕ → Bool) (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hlog : s.val.tapes archive = BitTape.atEnd saved) :
    Executes (preceding ++ b :: suffix) randomTape (.call (readBit archive)) 5 s
      (Store.ofState (readBitFinish archive b s.val)) ∧
    (readBitFinish archive b s.val).tapes archive = BitTape.atEnd (saved ++ [b]) ∧
    Frame {archive} s.val (readBitFinish archive b s.val) := by
  have hb : inputBit (preceding ++ b :: suffix) s.val.inputHead = b := by
    simp [inputBit, hhead]
  refine ⟨?_, ?_, ?_⟩
  · apply Executes.call (readBit archive) s (readBitFinish archive b s.val) 4
    · apply executeInstructions_sound (instructions := 4)
      simp [executeInstructions, BitRAM.next, readBit, readBitFinish, s.property, hb,
        BitRAMState.setRegister, BitRAMState.setTape, BitTape.write]
    · rfl
  · simpa [readBitFinish, hlog] using BitTape.append_write saved b
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [readBitFinish, hi]

/-- Read a self-delimiting natural, retain its exact codec in the archive,
and keep its binary value at the beginning of a dedicated metadata tape. -/
def readNat (target archive : ℕ) : Code :=
  .seq (.call (ParseNat.programOn target))
    (.seq (.call resetCounter)
      (.seq (.call (Rewind.program target))
        (.seq (.call (Copy.program target 11))
          (.seq (.call (LogNat.program 11 archive)) (.call (Rewind.program target))))))

def natWork (target archive : ℕ) : Finset ℕ := {10, 11, target, archive}

theorem readNat_steps (target archive : ℕ) (ht10 : target ≠ 10) (ht11 : target ≠ 11)
    (ha10 : archive ≠ 10) (ha11 : archive ≠ 11) (hta : target ≠ archive)
    (n : ℕ) (preceding suffix saved : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hcount : s.val.tapes 10 = BitTape.blank) (htarget : s.val.tapes target = BitTape.blank)
    (hcopy : s.val.tapes 11 = BitTape.blank) (hlog : s.val.tapes archive = BitTape.atEnd saved) :
    ∃ t : Store,
      Executes (preceding ++ (Codec.nat n ++ suffix)) randomTape (readNat target archive)
        (60 * n.bits.length + 57) s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.nat n).length ∧
      t.val.tapes target = BitTape.ofList n.bits ∧
      t.val.tapes archive = BitTape.atEnd (saved ++ Codec.nat n) ∧
      t.val.tapes 10 = BitTape.blank ∧ t.val.tapes 11 = BitTape.blank ∧
      Frame (natWork target archive) s.val t.val := by
  let input := preceding ++ (Codec.nat n ++ suffix)
  obtain ⟨p, hp, hppc, hphead, hpcount, hpword, hpframe⟩ :=
    ParseNat.parse_on_steps target ht10 n preceding suffix randomTape s.val s.property
      hhead hcount htarget
  have ep := Executes.call (ParseNat.programOn target) s p _ hp (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hppc,
      BitRAMInstruction.renameTapes])
  let p' := Store.ofState p
  have er := resetCounter_steps input randomTape p' hpcount
  let r := Store.ofState (resetCounterState p'.val)
  have hrword : r.val.tapes target = BitTape.atEnd n.bits := by
    simpa [r, p', resetCounterState, Store.ofState, ht10] using hpword
  have e1 := Executes.call (Rewind.program target) r (Rewind.finish target r.val) _
    (Rewind.atEnd_steps target input randomTape n.bits r.val r.property hrword)
    (by simp [Rewind.finish, Rewind.program])
  let u := Store.ofState (Rewind.finish target r.val)
  have huword : u.val.tapes target = BitTape.ofList n.bits :=
    Rewind.finish_tape target n.bits r.val hrword
  have hucopy : u.val.tapes 11 = BitTape.blank := by
    simpa [u, r, p', Store.ofState, Rewind.finish, resetCounterState, Ne.symm ht11] using
      (hpframe.2.2.2.2.1 11 (by decide) ht11.symm).trans hcopy
  obtain ⟨v, hv, hvpc, hvwrite, hvword, hvframe⟩ :=
    Copy.simulation target 11 ht11 input randomTape u.val n.bits u.property
      (by rw [huword]; exact BitTape.ofList_represents n.bits)
  have ev := Executes.call (Copy.program target 11) u v _ hv
    (by simp [Copy.program, hvpc])
  have hvtarget : v.tapes target = BitTape.atEnd n.bits := by
    simpa [huword, BitTape.atEnd, BitTape.ofList] using hvword
  have hvcopy : v.tapes 11 = BitTape.atEnd n.bits := by
    have hh := hvwrite.blank (show u.val.tapes 11 = {BitTape.blank with head := (0 : ℤ)} by
      simpa [BitTape.blank] using hucopy)
    simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hh
  have hulog : u.val.tapes archive = BitTape.atEnd saved := by
    simpa [u, r, p', Store.ofState, Rewind.finish, resetCounterState, ha10, hta.symm] using
      (hpframe.2.2.2.2.1 archive ha10 hta.symm).trans hlog
  have hvlog : v.tapes archive = BitTape.atEnd saved :=
    (hvframe.2.2.2.2.2.1 archive hta.symm ha11).trans hulog
  let v' := Store.ofState v
  have el := Executes.call (LogNat.program 11 archive) v'
    (LogNat.finish 11 archive n.bits saved v'.val) _
    (LogNat.steps 11 archive ha11.symm input randomTape n.bits saved v'.val rfl hvcopy hvlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  let w := Store.ofState (LogNat.finish 11 archive n.bits saved v'.val)
  have hlframe := LogNat.finish_frame 11 archive n.bits saved v'.val
  have hwtarget : w.val.tapes target = BitTape.atEnd n.bits :=
    (hlframe.2.2.2.2.2.1 target ht11 hta).trans hvtarget
  have e2 := Executes.call (Rewind.program target) w (Rewind.finish target w.val) _
    (Rewind.atEnd_steps target input randomTape n.bits w.val w.property hwtarget)
    (by simp [Rewind.finish, Rewind.program])
  let t := Store.ofState (Rewind.finish target w.val)
  have htapes (i : ℕ) (hi10 : i ≠ 10) (hi11 : i ≠ 11) (hit : i ≠ target)
      (hia : i ≠ archive) : t.val.tapes i = s.val.tapes i := by
    have h0 := hpframe.2.2.2.2.1 i hi10 hit
    have h1 : u.val.tapes i = s.val.tapes i := by
      simpa [u, r, p', Store.ofState, Rewind.finish, resetCounterState, hi10, hit] using h0
    have h2 := hvframe.2.2.2.2.2.1 i hit hi11
    have h3 := hlframe.2.2.2.2.2.1 i hi11 hia
    simpa [t, w, v', Store.ofState, Rewind.finish, hit] using h3.trans (h2.trans h1)
  refine ⟨t, ?_, ?_, Rewind.finish_tape target n.bits w.val hwtarget, ?_, ?_, ?_, ?_⟩
  · convert ep.seq (er.seq (e1.seq (ev.seq (el.seq e2)))) using 1 <;> first | rfl | omega
  · exact hlframe.2.1.trans (hvframe.2.1.trans hphead)
  · have hh := LogNat.finish_target 11 archive ha11.symm n.bits saved v'.val
    simpa [t, w, Store.ofState, Rewind.finish, hta.symm, LogNat.word_bits] using hh
  · have hu10 : u.val.tapes 10 = BitTape.blank := by
      simp [u, r, Store.ofState, Rewind.finish, resetCounterState, ht10.symm]
    have hv10 := (hvframe.2.2.2.2.2.1 10 ht10.symm (by decide)).trans hu10
    have hw10 := (hlframe.2.2.2.2.2.1 10 (by decide) ha10.symm).trans hv10
    simpa [t, w, v', Store.ofState, Rewind.finish, ht10.symm] using hw10
  · have hh := LogNat.finish_source 11 archive n.bits saved v'.val
    simpa [t, w, Store.ofState, Rewind.finish, ht11.symm] using hh
  · refine ⟨hlframe.1.trans (hvframe.1.trans hpframe.1),
      hlframe.2.2.1.trans (hvframe.2.2.1.trans hpframe.2.1),
      hlframe.2.2.2.1.trans (hvframe.2.2.2.1.trans hpframe.2.2.1),
      hlframe.2.2.2.2.1.trans (hvframe.2.2.2.2.1.trans hpframe.2.2.2.1), ?_⟩
    intro i hi
    simp only [natWork, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact htapes i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2

end Maxwell.Cost.DecoderParser
