import Maxwell.Cost.MagnitudeMax.Parse
import Maxwell.Cost.MagnitudeMax.Initialize

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

/-- One fixed finite program parses the list count, scans every signed
rational, retains the full list, and stores a selected magnitude pair. -/
def code : Code := .seq initializeCode Parse.code

def program : BitRAM := code.compile

def price (qs : List ℚ) (B : ℕ) : ℕ := 4 + Parse.price qs B

theorem executes (qs : List ℚ) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ price qs B ∧
      Executes (Codec.list Codec.rat qs ++ suffix) tape code cost
        (Store.ofState BitRAMState.initial) t ∧
      t.val.inputHead = (Codec.list Codec.rat qs).length ∧
      Bank t.val (bankOf (maximum qs)) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      t.val.tapes 20 = BitTape.atEnd (Loop.records qs) ∧
      t.val.address = [] ∧ t.val.memory = BitRAMState.initial.memory ∧
      t.val.randomCursor = 0 ∧ t.val.output = [] := by
  let s := Store.ofState BitRAMState.initial
  have hb : Bank s.val (bankOf (0, 0)) := by
    intro i _ _
    refine ⟨0, ?_⟩
    simp [s, Store.ofState, BitRAMState.initial, bankOf, BitTape.blank, BitTape.ofList]
  have hr : Scratch (initialized s).val 0 := by
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [initialized, s, Store.ofState, BitRAMState.initial, BitTape.blank, BitTape.ofList]
  have hp : LogRat.Ready (initialized s).val := by
    simp [LogRat.Ready, initialized, s, Store.ofState, BitRAMState.initial]
  obtain ⟨c, t, hc, ht, hthead, htb, htr, htp, htlog, htf⟩ :=
    Parse.executes qs (0, 1) B [] suffix [] tape (initialized s) rfl rfl (by decide)
      (by simp [hB]) hwidth (initialized_bank s hb) hr hp (by
        simp [initialized, s, Store.ofState, BitRAMState.initial, BitTape.atEnd, BitTape.ofList, BitTape.blank])
  have hi := initialize_executes (Codec.list Codec.rat qs ++ suffix) tape s rfl
  refine ⟨4 + c, t, by dsimp [price]; omega, ?_, ?_, htb, htr, htp, ?_,
    htf.1, htf.2.1, htf.2.2.1, htf.2.2.2.1⟩
  · exact hi.seq (by simpa using ht)
  · simpa [initialized, s, Store.ofState, BitRAMState.initial] using hthead
  · simpa using htlog

set_option maxRecDepth 8192 in
/-- Genuine capped BitRAM execution, including the header and initial 0/1
write. The result is an original raw pair, so stored widths never grow. -/
theorem run (qs : List ℚ) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (Codec.list Codec.rat qs ++ suffix) tape (price qs B + 1)).finished = some final ∧
      (program.run (Codec.list Codec.rat qs ++ suffix) tape (price qs B + 1)).instructions ≤ price qs B ∧
      final.inputHead = (Codec.list Codec.rat qs).length ∧
      Word final 30 (maximum qs).1 ∧ Word final 31 (maximum qs).2 ∧
      value (maximum qs) = Logical.Normalization.magnitudeMax qs ∧
      (maximum qs).1.bits.length ≤ B ∧ (maximum qs).2.bits.length ≤ B ∧
      final.tapes 20 = BitTape.atEnd (Loop.records qs) ∧
      final.randomCursor = 0 ∧ final.output = [] := by
  obtain ⟨c, t, hc, ht, hhead, hbank, _, _, hlog, _, _, hrandom, hout⟩ :=
    executes qs B hB hwidth suffix tape
  obtain ⟨hrun, hcost⟩ := ht.compiled_run (price qs B + 1) (by omega)
  obtain ⟨hnum, hden⟩ := maximum_width qs B B hB
    (fun q hq => (hwidth q hq).1) (fun q hq => (hwidth q hq).2)
  refine ⟨t.place code.size, hrun, ?_, hhead, ?_, ?_, maximum_value qs,
    hnum, hden, hlog, hrandom, hout⟩
  · exact (le_of_eq hcost).trans hc
  · simpa [bankOf, Word, Store.place] using hbank 30 (by decide) (by decide)
  · simpa [bankOf, Word, Store.place] using hbank 31 (by decide) (by decide)

end Maxwell.Cost.MagnitudeMax
