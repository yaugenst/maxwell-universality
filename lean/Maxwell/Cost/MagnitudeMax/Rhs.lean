import Maxwell.Cost.MagnitudeMax.Parse

namespace Maxwell.Cost.MagnitudeMax.Rhs

open Structured RationalAccumulator

/-- The rational maximum parser reuses counter 21, leaving the sparse
record counter and all retained matrix metadata alone. -/
def permutation : Equiv.Perm ℕ := Equiv.swap 14 21

def program : BitRAM := Parse.code.compile.renameTapes permutation

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 21 → i ≠ 20 →
    (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i)

set_option maxRecDepth 8192 in
theorem executes (qs : List ℚ) (current : Pair) (B : ℕ)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hcounter : s.val.tapes 21 = BitTape.blank)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogRat.Ready s.val) (harchive : s.val.tapes 20 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ Parse.price qs B + 1 ∧
      Executes (preceding ++ (Codec.list Codec.rat qs ++ suffix)) tape (.call program) cost s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.list Codec.rat qs).length ∧
      Bank t.val (bankOf (scan current qs)) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      t.val.tapes 20 = BitTape.atEnd (archive ++ Loop.records qs) ∧ Frame s.val t.val := by
  let u := Store.ofState (s.val.renameTapes permutation.symm)
  have huother (i : ℕ) (h14 : i ≠ 14) (h21 : i ≠ 21) : u.val.tapes i = s.val.tapes i := by
    simp [u, Store.ofState, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def, h14, h21]
  have hub : Bank u.val (bankOf current) := by
    intro i hi hi'
    exact word_of_eq (huother i (by omega) (by omega)) (hbank i hi hi')
  have hur : Scratch u.val 0 :=
    ⟨blank_of_eq (huother 0 (by decide) (by decide)) hready.1,
      word_of_eq (huother 1 (by decide) (by decide)) hready.2.1,
      blank_of_eq (huother 2 (by decide) (by decide)) hready.2.2.1,
      blank_of_eq (huother 3 (by decide) (by decide)) hready.2.2.2⟩
  have hup : LogRat.Ready u.val :=
    ⟨(huother 10 (by decide) (by decide)).trans hparser.1,
      (huother 12 (by decide) (by decide)).trans hparser.2.1,
      (huother 13 (by decide) (by decide)).trans hparser.2.2⟩
  obtain ⟨c, v, hc, hv, hvhead, hvb, hvr, hvp, hvlog, hvf⟩ := Parse.executes qs current B preceding suffix archive
    tape u hhead (by simpa [u, Store.ofState, BitRAMState.renameTapes, permutation] using hcounter)
    hpositive hcurrent hwidth hub hur hup ((huother 20 (by decide) (by decide)).trans harchive)
  let result := (v.place Parse.code.size).renameTapes permutation
  have he := hv.compiled_steps.renameTapes permutation
  have hs0 : {s.val with pc := 0} = s.val :=
    (congrArg (fun pc => {s.val with pc := pc}) s.property).symm
  have he' : PricedSteps (program.next (preceding ++ (Codec.list Codec.rat qs ++ suffix)) tape) c s.val result := by
    simpa only [u, Store.ofState, BitRAMState.renameTapes, s.property, Function.comp_def,
      Equiv.symm_apply_apply, result, program, hs0] using he
  have hh : program.code[result.pc]? = some .halt := by
    simp [program, result, Store.place, BitRAMState.renameTapes, BitRAM.renameTapes,
      Parse.code.compile_halt, BitRAMInstruction.renameTapes]
  have htother (i : ℕ) (h14 : i ≠ 14) (h21 : i ≠ 21) : (Store.ofState result).val.tapes i = v.val.tapes i := by
    simp [result, Store.ofState, Store.place, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def, h14, h21]
  refine ⟨c + 1, Store.ofState result, by omega, Executes.call _ _ _ _ he' hh, hvhead, ?_, ?_, ?_,
    (htother 20 (by decide) (by decide)).trans hvlog, ?_⟩
  · intro i hi hi'
    exact word_of_eq (htother i (by omega) (by omega)) (hvb i hi hi')
  · exact ⟨blank_of_eq (htother 0 (by decide) (by decide)) hvr.1,
      word_of_eq (htother 1 (by decide) (by decide)) hvr.2.1,
      blank_of_eq (htother 2 (by decide) (by decide)) hvr.2.2.1,
      blank_of_eq (htother 3 (by decide) (by decide)) hvr.2.2.2⟩
  · exact ⟨(htother 10 (by decide) (by decide)).trans hvp.1,
      (htother 12 (by decide) (by decide)).trans hvp.2.1,
      (htother 13 (by decide) (by decide)).trans hvp.2.2⟩
  · refine ⟨hvf.1, hvf.2.1, hvf.2.2.1, hvf.2.2.2.1, ?_⟩
    intro i h4 h10 h12 h13 h21 h20 hb
    by_cases h14 : i = 14
    · subst i
      have h := hvf.2.2.2.2 21 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (Or.inl (by decide))
      simpa [result, Store.ofState, Store.place, u, BitRAMState.renameTapes, permutation] using h
    · exact (htother i h14 h21).trans
        ((hvf.2.2.2.2 i h4 h10 h12 h13 h14 h20 hb).trans (huother i h14 h21))

end Maxwell.Cost.MagnitudeMax.Rhs
