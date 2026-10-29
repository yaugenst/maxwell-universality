import Maxwell.Cost.MagnitudeMax.Initialize
import Maxwell.Cost.MagnitudeMax.Save

namespace Maxwell.Cost.MagnitudeMax.Reset

open Structured RationalAccumulator

private theorem blank_write_one (origin : ℤ) :
    ({BitTape.blank with head := origin}).write (some true) = BitTape.shifted [true] origin := by
  apply BitTape.ext
  · rfl
  · have h := congrArg BitTape.cells (BitTape.shiftedEnd_append_write [] origin true)
    simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using h

def seed (s : Store) : Store :=
  let u := Store.ofState (s.val.setRegister 61 true)
  Store.ofState (u.val.setTape 31 ((u.val.tapes 31).write (some (u.val.registers 61))))

theorem seed_steps (input : List Bool) (tape : ℕ → Bool) (s : Store) (hblank : Blank s.val 31) :
    Executes input tape initializeCode 4 s (seed s) ∧ Word (seed s).val 31 1 ∧
      (seed s).val.inputHead = s.val.inputHead ∧ DecoderParser.Frame {31} s.val (seed s).val := by
  have h1 := Executes.literal input tape s 61 true
  have h2 := Executes.writeTape input tape (Store.ofState (s.val.setRegister 61 true)) 31 61
  obtain ⟨origin, ho⟩ := hblank
  refine ⟨h1.seq h2, ⟨origin, ?_⟩, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [seed, Store.ofState, BitRAMState.setRegister, BitRAMState.setTape, ho, blank_write_one]
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [seed, Store.ofState, BitRAMState.setRegister, BitRAMState.setTape, hi]

def work : Finset ℕ := {0, 1, 2, 3, 30, 31, 32, 33, 34, 35, 36}

def code : Code := .seq (.call (TapeOps.clear 30)) (.seq (.call (TapeOps.clear 31)) initializeCode)

theorem executes (p : Pair) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : Bank s.val (bankOf p)) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape code (6 * (p.1.bits.length + p.2.bits.length) + 12) s t ∧
      Bank t.val (bankOf (0, 1)) ∧ Scratch t.val 0 ∧
      t.val.inputHead = s.val.inputHead ∧ DecoderParser.Frame work s.val t.val := by
  obtain ⟨u, hu, hub, hur, huf⟩ := clear_bank 30 (by decide) (by decide) input tape (bankOf p) 0 s hbank hready
  obtain ⟨v, hv, hvb, hvr, hvf⟩ := clear_bank 31 (by decide) (by decide) input tape
    (Function.update (bankOf p) 30 0) 0 u hub hur
  have hzero : Function.update (Function.update (bankOf p) 30 0) 31 0 = bankOf (0, 0) := by
    funext i
    by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;>
      simp_all [bankOf]
  rw [hzero] at hvb
  have hvblank : Blank v.val 31 := (zero_word_iff_blank v.val 31).mp (by simpa [bankOf] using hvb 31 (by decide) (by decide))
  obtain ⟨he, he31, hehead, hef⟩ := seed_steps input tape v hvblank
  refine ⟨seed v, ?_, ?_, ?_, hehead.trans (hvf.2.1.trans huf.2.1), ?_⟩
  · norm_num [bankOf] at hu hv
    convert hu.seq (hv.seq he) using 1 <;> first | rfl | omega
  · intro i hi hi'
    by_cases h31 : i = 31
    · subst i; simpa [bankOf] using he31
    · have h := word_of_eq (hef.tapes i (by simpa using h31)) (hvb i hi hi')
      simpa [bankOf, h31] using h
  · exact ⟨blank_of_eq (hef.tapes 0 (by simp)) hvr.1, word_of_eq (hef.tapes 1 (by simp)) hvr.2.1,
      blank_of_eq (hef.tapes 2 (by simp)) hvr.2.2.1, blank_of_eq (hef.tapes 3 (by simp)) hvr.2.2.2⟩
  · refine ⟨hef.address.trans (hvf.1.trans huf.1), hef.memory.trans (hvf.2.2.1.trans huf.2.2.1),
      hef.randomCursor.trans (hvf.2.2.2.1.trans huf.2.2.2.1),
      hef.output.trans (hvf.2.2.2.2.1.trans huf.2.2.2.2.1), ?_⟩
    intro i hi
    simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have h4 : 4 ≤ i := by omega
    have hb : i < 30 ∨ 36 < i := by omega
    exact (hef.tapes i (by simp; omega)).trans
      ((hvf.2.2.2.2.2.1 i h4 hb).trans (huf.2.2.2.2.2.1 i h4 hb))

end Maxwell.Cost.MagnitudeMax.Reset
