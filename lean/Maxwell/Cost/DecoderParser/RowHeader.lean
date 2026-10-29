import Maxwell.Cost.DecoderParser.ReadFields
import Maxwell.Cost.RationalAccumulator.Initialize

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank Scratch Word Blank)

theorem Frame.bank {work : Finset ℕ} {s t : BitRAMState} (hf : Frame work s t)
    (hwork : ∀ i, 30 ≤ i → i ≤ 36 → i ∉ work) {v : ℕ → ℕ} (hb : Bank s v) : Bank t v := by
  intro i hi hi'
  exact RationalAccumulator.word_of_eq (hf.tapes i (hwork i hi hi')) (hb i hi hi')

theorem Frame.scratch {work : Finset ℕ} {s t : BitRAMState} (hf : Frame work s t)
    (hwork : ∀ i, i < 4 → i ∉ work) {scalar : ℕ} (hr : Scratch s scalar) : Scratch t scalar :=
  ⟨RationalAccumulator.blank_of_eq (hf.tapes 0 (hwork 0 (by decide))) hr.1,
    RationalAccumulator.word_of_eq (hf.tapes 1 (hwork 1 (by decide))) hr.2.1,
    RationalAccumulator.blank_of_eq (hf.tapes 2 (hwork 2 (by decide))) hr.2.2.1,
    RationalAccumulator.blank_of_eq (hf.tapes 3 (hwork 3 (by decide))) hr.2.2.2⟩

/-- Read the rational row offset into the actual arithmetic bank, then
read the support count into the row's private finite countdown tape. -/
def rowHeaderCode : Code := .seq readRational
  (.seq RationalAccumulator.initializeCode (readNatural 73))

def rowHeaderPrice (v : ℕ → ℕ) (q : ℚ) (count : ℕ) : ℕ :=
  6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length)+
    38*(q.num.natAbs.bits.length+q.den.bits.length)+21*count.bits.length+96

def rowWork : Finset ℕ := {0,1,2,3,12,13,30,31,32,33,34,35,36,73}

theorem rowHeader_steps (q : ℚ) (count : ℕ) (v : ℕ → ℕ)
    (preceding suffix : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hh : s.val.inputHead=preceding.length) (hb : Bank s.val v) (hr : Scratch s.val 0)
    (h10 : s.val.tapes 10=BitTape.blank) (h12 : s.val.tapes 12=BitTape.blank)
    (h13 : s.val.tapes 13=BitTape.blank) (h73 : s.val.tapes 73=BitTape.blank) :
    ∃ t : Store,
      Executes (preceding ++ (Codec.rat q ++ (Codec.nat count ++ suffix))) randomTape
        rowHeaderCode (rowHeaderPrice v q count) s t ∧
      t.val.inputHead=s.val.inputHead+(Codec.rat q++Codec.nat count).length ∧
      Bank t.val (RationalAccumulator.initialized v (Codec.RationalPair.canonical q)) ∧
      Scratch t.val 0 ∧ t.val.tapes 73=BitTape.ofList count.bits ∧
      t.val.tapes 10=BitTape.blank ∧ t.val.tapes 12=BitTape.blank ∧
      t.val.tapes 13=BitTape.blank ∧ Frame rowWork s.val t.val := by
  let input := preceding ++ (Codec.rat q ++ (Codec.nat count ++ suffix))
  obtain ⟨u,eu,huh,hu10,hu12,hu13,hus,huf⟩ := readRational_steps q preceding
    (Codec.nat count++suffix) randomTape s hh h10 h12 h13
  have hub := huf.bank (by intro i hi hi';simp;omega) hb
  have hur := huf.scratch (by intro i hi;simp;omega) hr
  obtain ⟨a,ea,hab,har,ha12,ha13,haf⟩ := RationalAccumulator.initialize_bank input randomTape v
    (Codec.RationalPair.canonical q) u hub hur hu12 hu13 hus
  have ha10 : a.val.tapes 10=BitTape.blank :=
    (haf.2.2.2.2.2.1 10 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hu10
  have ha73 : a.val.tapes 73=BitTape.blank :=
    (haf.2.2.2.2.2.1 73 (by decide) (by decide) (by decide) (Or.inr (by decide))).trans
      ((huf.tapes 73 (by decide)).trans h73)
  obtain ⟨t,et,hth,ht73,ht10,htf⟩ := readNatural_steps 73 (by decide) count
    (preceding++Codec.rat q) suffix randomTape a
    (by simp [haf.2.1,huh,hh]) ha10 ha73
  have hi : (preceding++Codec.rat q)++(Codec.nat count++suffix)=input := by
    simp [input,List.append_assoc]
  rw [hi] at et
  refine ⟨t,?_,?_,htf.bank (by intro i hi hi';simp;omega) hab,
    htf.scratch (by intro i hi;simp;omega) har,ht73,ht10,
    (htf.tapes 12 (by decide)).trans ha12,(htf.tapes 13 (by decide)).trans ha13,?_⟩
  · convert eu.seq (ea.seq et) using 1 <;> first | rfl | (dsimp [rowHeaderPrice,Codec.RationalPair.canonical];omega)
  · simp only [List.length_append,Nat.cast_add]
    have hi := haf.2.1
    omega
  · refine ⟨htf.address.trans (haf.1.trans huf.address),
      htf.memory.trans (haf.2.2.1.trans huf.memory),
      htf.randomCursor.trans (haf.2.2.2.1.trans huf.randomCursor),
      htf.output.trans (haf.2.2.2.2.1.trans huf.output),?_⟩
    intro i hi
    have hin : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 12 ∧ i ≠ 13 ∧
        i ≠ 30 ∧ i ≠ 31 ∧ i ≠ 32 ∧ i ≠ 33 ∧ i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 36 ∧ i ≠ 73 := by
      simpa only [rowWork,Finset.mem_insert,Finset.mem_singleton,not_or] using hi
    exact (htf.tapes i (by simp;tauto)).trans
      ((haf.2.2.2.2.2.1 i (by omega) (by tauto) (by tauto) (by omega)).trans
        (huf.tapes i (by simp;tauto)))

end Maxwell.Cost.DecoderParser
