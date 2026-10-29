import Maxwell.Cost.SignedRound.Value
import Maxwell.Cost.SignedRound.Remainder
import Maxwell.Cost.SignedRound.Quotient

namespace Maxwell.Cost.SignedRound

open Structured RationalAccumulator

def incrementFlag (negative : Bool) (numerator denominator : ℕ) : Bool :=
  if negative then decide (denominator < 2 * (numerator % denominator))
  else decide (denominator ≤ 2 * (numerator % denominator))

theorem incrementFlag_value (negative : Bool) (numerator denominator : ℕ) :
    (incrementFlag negative numerator denominator).toNat = increment negative numerator denominator := by
  cases negative <;> simp only [incrementFlag, increment, Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs <;> simp_all

def code : Code := .seq (.call Division.program)
  (.seq Remainder.code (.seq Quotient.code
    (.seq (Code.atom (.tapeRight 3)) (.call (TapeOps.clear 3)))))

/-- One fixed finite program rounds a signed rational magnitude. Input tape
3 is consumed and cleared; the positive denominator on tape 1 is restored.
The output magnitude on tape 4 and sign in register 23 use canonical zero. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (negative : Bool) (numerator denominator : ℕ) (hd : 0 < denominator)
    (ao xo zo yo qo : ℤ)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted denominator.bits xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = BitTape.shiftedEnd numerator.bits yo)
    (h4 : s.val.tapes 4 = {BitTape.blank with head := qo})
    (hsign : s.val.registers 35 = negative) :
    ∃ cost, ∃ t : Store, ∃ origin : ℤ,
      cost ≤ 3000 * (numerator.bits.length + denominator.bits.length + 2)^2 ∧
      Executes input tape code cost s t ∧
      t.val.tapes 4 = BitTape.shifted (magnitude negative numerator denominator).bits origin ∧
      t.val.registers 23 = decide (rounded negative numerator denominator < 0) ∧
      t.val.tapes 1 = BitTape.shifted denominator.bits xo ∧
      Blank t.val 0 ∧ Blank t.val 2 ∧ Blank t.val 3 ∧ Frame 5 s.val t.val := by
  obtain ⟨divCost, divided, remainder, quotient, ro, so, qro, hdCost, hed, hdp,
      hd0, hd1, hd2, hd4, hrValue, hqValue, hrLen, hqLen, hd3⟩ :=
    Division.simulation_cleanup input tape s.val denominator.bits numerator.bits ao xo zo yo qo
      (by simpa using hd) s.property h0 h1 h2 h3 h4
  have hdf := Division.execution_frame input tape hed
  let d : Store := Store.ofState divided
  have hed' : Executes input tape (.call Division.program) (divCost + 1) s d :=
    Executes.call _ _ _ _ hed (by
      simp [Division.program, hdp, Subtraction.program, RewindOvershoot.program,
        RewindOvershoot.preamble, BitRAM.link, Rewind.program, TapeOps.clear,
        TapeOps.copyClear, BitRAMInstruction.relocate])
  have hdsg : d.val.registers 35 = negative := (frame_of_division hdf).sign.trans hsign
  obtain ⟨remCost, r, hrCost, her, hrflag, hr0, hr1, hr2, hrf⟩ :=
    Remainder.executes input tape d remainder denominator hd ro xo so negative hd0 hd1 hd2 hdsg
  let flag := incrementFlag negative numerator denominator
  have hrFlag : r.val.registers 36 = flag := by
    simpa [flag, incrementFlag, hrValue] using hrflag
  have hr4 : r.val.tapes 4 = BitTape.shifted quotient qro :=
    (hrf.2.2.2.2.2.1 4 (by omega)).trans hd4
  have hrsg : r.val.registers 35 = negative := hrf.sign.trans hdsg
  obtain ⟨quoCost, q, hqCost, heq, hq4, hqSign, hqt, hqf⟩ :=
    Quotient.executes input tape r quotient qro negative flag hr4 hrsg hrFlag
  have hvalue : addressValue quotient + flag.toNat = magnitude negative numerator denominator := by
    simpa [flag, magnitude, incrementFlag_value] using congrArg
      (fun n => n + increment negative numerator denominator) hqValue
  have hq3 : q.val.tapes 3 = {BitTape.shifted numerator.bits yo with head := yo - 1} :=
    (hqt 3 (by omega)).trans ((hrf.2.2.2.2.2.1 3 (by omega)).trans hd3)
  let a : Store := Store.ofState (q.val.setTape 3 {q.val.tapes 3 with head := (q.val.tapes 3).head + 1})
  have hea : Executes input tape (Code.atom (.tapeRight 3)) 2 q a :=
    Executes.tapeRight input tape q 3
  have ha3 : a.val.tapes 3 = BitTape.shifted numerator.bits yo := by
    simp [a, Store.ofState, BitRAMState.setTape, hq3, BitTape.shifted]
  have haf : Frame 5 q.val a.val := by
    simp [Frame, a, Store.ofState, BitRAMState.setTape]
    intro i hi; simp [show i ≠ 3 by omega]
  obtain ⟨cleared, ht, htp, ht3, htf⟩ := TapeOps.clear_steps 3 input tape numerator.bits yo
    a.val a.property ha3
  let t : Store := Store.ofState cleared
  have het : Executes input tape (.call (TapeOps.clear 3)) (6 * numerator.bits.length + 4) a t :=
    Executes.call _ _ _ _ ht (by simp [TapeOps.clear, htp])
  have hlast : Frame 5 q.val t.val := haf.trans
    (frame_of_transfer (by omega) (by omega) (WordTransfer.frame_of_copy htf))
  have hother : ∀ i, i ≠ 3 → t.val.tapes i = q.val.tapes i := by
    intro i hi
    have hh := htf.2.2.2.2.2.1 i hi hi
    simpa [t, a, Store.ofState, BitRAMState.setTape, hi] using hh
  refine ⟨(divCost + 1) + (remCost + (quoCost + (2 + (6 * numerator.bits.length + 4)))),
    t, qro, ?_, hed'.seq (her.seq (heq.seq (hea.seq het))), ?_, ?_, ?_, ?_, ?_,
    ⟨yo + numerator.bits.length, ht3⟩,
    (((frame_of_division hdf).trans (hrf.mono (by omega))).trans hqf).trans hlast⟩
  · nlinarith
  · have hh := (hother 4 (by omega)).trans hq4
    simpa only [hvalue] using hh
  · have hsg : t.val.registers 23 = q.val.registers 23 :=
      htf.2.2.2.2.2.2 23 (by omega) (by omega)
    rw [hsg, hqSign, hvalue]
    cases negative <;> simp [rounded]
  · exact (hother 1 (by omega)).trans ((hqt 1 (by omega)).trans hr1)
  · exact blank_of_eq ((hother 0 (by omega)).trans (hqt 0 (by omega))) hr0
  · exact blank_of_eq ((hother 2 (by omega)).trans (hqt 2 (by omega))) hr2

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (negative : Bool) (numerator denominator : ℕ) (hd : 0 < denominator)
    (ao xo zo yo qo : ℤ)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted denominator.bits xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = BitTape.shiftedEnd numerator.bits yo)
    (h4 : s.val.tapes 4 = {BitTape.blank with head := qo})
    (hsign : s.val.registers 35 = negative) :
    ∃ t : Store, ∃ origin : ℤ,
      (runPriced (code.compile.next input tape)
        (3000 * (numerator.bits.length + denominator.bits.length + 2)^2 + 1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape)
        (3000 * (numerator.bits.length + denominator.bits.length + 2)^2 + 1) s.val).instructions ≤
        3000 * (numerator.bits.length + denominator.bits.length + 2)^2 ∧
      t.val.tapes 4 = BitTape.shifted (magnitude negative numerator denominator).bits origin ∧
      t.val.registers 23 = decide (rounded negative numerator denominator < 0) ∧
      t.val.tapes 1 = BitTape.shifted denominator.bits xo ∧
      Blank t.val 0 ∧ Blank t.val 2 ∧ Blank t.val 3 ∧ Frame 5 s.val t.val := by
  obtain ⟨cost, t, origin, hc, he, hmag, hs, hden, hzero, htwo, hthree, hf⟩ :=
    executes input tape s negative numerator denominator hd ao xo zo yo qo h0 h1 h2 h3 h4 hsign
  have hr := he.compiled_run (3000 * (numerator.bits.length + denominator.bits.length + 2)^2 + 1) (by omega)
  exact ⟨t, origin, hr.1, hr.2 ▸ hc, hmag, hs, hden, hzero, htwo, hthree, hf⟩

end Maxwell.Cost.SignedRound
