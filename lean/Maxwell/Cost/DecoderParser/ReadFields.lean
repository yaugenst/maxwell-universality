import Maxwell.Cost.DecoderParser.Primitives
import Maxwell.Cost.ParseRat

namespace Maxwell.Cost.DecoderParser
open Structured

/-- A value retained for arithmetic, with no redundant archive copy. -/
def readNatural (target : ℕ) : Code := .seq (.call (ParseNat.programOn target))
  (.seq (.call resetCounter) (.call (Rewind.program target)))

theorem readNatural_steps (target : ℕ) (ht : target ≠ 10)
    (n : ℕ) (preceding suffix : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hh : s.val.inputHead = preceding.length) (h10 : s.val.tapes 10 = BitTape.blank)
    (hblank : s.val.tapes target = BitTape.blank) :
    ∃ t : Store, Executes (preceding ++ (Codec.nat n ++ suffix)) randomTape
      (readNatural target) (21*n.bits.length+16) s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.nat n).length ∧
      t.val.tapes target = BitTape.ofList n.bits ∧ t.val.tapes 10 = BitTape.blank ∧
      Frame {target} s.val t.val := by
  let input := preceding ++ (Codec.nat n ++ suffix)
  obtain ⟨u,hu,hup,huh,hu10,huword,huf⟩ := ParseNat.parse_on_steps target ht n preceding suffix
    randomTape s.val s.property hh h10 hblank
  have e1 := Executes.call (ParseNat.programOn target) s u _ hu (by
    simp [ParseNat.programOn,BitRAM.renameTapes,ParseNat.program,hup,BitRAMInstruction.renameTapes])
  let u' := Store.ofState u
  have e2 := resetCounter_steps input randomTape u' hu10
  let v := Store.ofState (resetCounterState u'.val)
  have hvword : v.val.tapes target = BitTape.atEnd n.bits := by
    simpa [v,u',Store.ofState,resetCounterState,ht] using huword
  have e3 := Executes.call (Rewind.program target) v (Rewind.finish target v.val) _
    (Rewind.atEnd_steps target input randomTape n.bits v.val v.property hvword)
    (by simp [Rewind.program,Rewind.finish])
  let t := Store.ofState (Rewind.finish target v.val)
  have ht10 : t.val.tapes 10 = BitTape.blank := by
    simp [t,v,Store.ofState,Rewind.finish,resetCounterState,ht.symm]
  refine ⟨t,?_,huh,Rewind.finish_tape target n.bits v.val hvword,ht10,?_⟩
  · convert e1.seq (e2.seq e3) using 1 <;> first | rfl | omega
  · refine ⟨huf.1,huf.2.1,huf.2.2.1,huf.2.2.2.1,?_⟩
    intro i hi
    have hit : i ≠ target := by simpa using hi
    by_cases hi10 : i = 10
    · subst i;exact ht10.trans h10.symm
    simpa [t,v,u',Store.ofState,Rewind.finish,resetCounterState,hit,hi10] using
      huf.2.2.2.2.1 i hi10 hit

def readRational : Code := .seq (.call ParseRat.program) (.call resetCounter)

theorem readRational_steps (q : ℚ) (preceding suffix : List Bool)
    (randomTape : ℕ → Bool) (s : Store) (hh : s.val.inputHead = preceding.length)
    (h10 : s.val.tapes 10 = BitTape.blank) (h12 : s.val.tapes 12 = BitTape.blank)
    (h13 : s.val.tapes 13 = BitTape.blank) :
    ∃ t : Store, Executes (preceding ++ (Codec.rat q ++ suffix)) randomTape readRational
      (17*(q.num.natAbs.bits.length+q.den.bits.length)+23) s t ∧
      t.val.inputHead = s.val.inputHead+(Codec.rat q).length ∧
      t.val.tapes 10 = BitTape.blank ∧
      t.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits ∧
      t.val.tapes 13 = BitTape.atEnd q.den.bits ∧
      t.val.registers 23 = decide (q.num < 0) ∧ Frame {12,13} s.val t.val := by
  obtain ⟨u,hu,hup,huh,hu10,hu12,hu13,hus,huf⟩ := ParseRat.parse_rat_steps q preceding suffix
    randomTape s.val s.property hh h10 h12 h13
  have e1 := Executes.call ParseRat.program s u _ hu (by simpa [hup] using (show ParseRat.program.code[42]? = some .halt by decide))
  have e2 := resetCounter_steps (preceding ++ (Codec.rat q ++ suffix)) randomTape (Store.ofState u) hu10
  let t := Store.ofState (resetCounterState (Store.ofState u).val)
  refine ⟨t,?_,huh,by simp [t,Store.ofState,resetCounterState],?_,?_,hus,?_⟩
  · convert e1.seq e2 using 1; rfl
  · simpa [t,Store.ofState,resetCounterState] using hu12
  · simpa [t,Store.ofState,resetCounterState] using hu13
  · refine ⟨huf.1,huf.2.1,huf.2.2.1,huf.2.2.2.1,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    by_cases hi10 : i = 10
    · subst i;simp [t,Store.ofState,resetCounterState,h10]
    simpa [t,Store.ofState,resetCounterState,hi10] using huf.2.2.2.2.1 i hi10 hi.1 hi.2

end Maxwell.Cost.DecoderParser
