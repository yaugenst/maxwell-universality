import Maxwell.Cost.SignedRound.Decision

namespace Maxwell.Cost.SignedRound.Quotient

open Structured

def bumpCode : Code := .branch 36
  (.seq (.call (Increment.program 4)) (.call (Rewind.program 4))) .skip

theorem bump (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (word : List Bool) (origin : ℤ) (flag : Bool)
    (hw : s.val.tapes 4 = BitTape.shifted word origin) (hf : s.val.registers 36 = flag) :
    ∃ cost, ∃ t : Store, ∃ result : List Bool,
      cost ≤ 12 * word.length + 20 ∧ Executes input tape bumpCode cost s t ∧
      result.length ≤ word.length + 1 ∧ addressValue result = addressValue word + flag.toNat ∧
      t.val.tapes 4 = BitTape.shifted result origin ∧
      (∀ i, i ≠ 4 → t.val.tapes i = s.val.tapes i) ∧ Frame 5 s.val t.val := by
  cases flag
  · exact ⟨2, s, word, by omega, Executes.no hf (Executes.skip s), by omega,
      by simp, hw, fun _ _ => rfl, Frame.refl 5 s.val⟩
  · obtain ⟨incCost, inc, hiCost, hi, hip, hi4, hif⟩ :=
      Increment.simulation 4 input tape word origin s.val s.property hw
    let a : Store := Store.ofState inc
    have hea : Executes input tape (.call (Increment.program 4)) (incCost + 1) s a :=
      Executes.call _ _ _ _ hi (by simp [Increment.program, hip])
    have hr := WordTransfer.rewind_shifted 4 origin input tape (Increment.bits word)
      a.val a.property hi4
    let t : Store := Store.ofState (Rewind.finishAt 4 origin a.val)
    have het : Executes input tape (.call (Rewind.program 4))
        (4 * (Increment.bits word).length + 6) a t :=
      Executes.call _ _ _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
    refine ⟨1 + ((incCost + 1) + (4 * (Increment.bits word).length + 6)), t,
      Increment.bits word, ?_, Executes.yes hf (hea.seq het), Increment.bits_length_le _,
      Increment.bits_value _, hr.2, ?_,
      (frame_of_increment (by omega) hif).trans (frame_rewind 5 4 (by omega) origin a.val)⟩
    · have hl := Increment.bits_length_le word
      omega
    · intro i hi
      have hh := hif.2.2.2.2.2.1 i hi
      simpa [t, a, Store.ofState, Rewind.finishAt, hi] using hh

def signProgram : BitRAM := ⟨[.readTape 4 26 27, .bitAnd 23 35 27, .halt]⟩

def signedState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 2
    registers := Function.update (Function.update (Function.update s.registers 26
      ((s.tapes 4).read.getD false)) 27 ((s.tapes 4).read.isSome))
      23 (s.registers 35 && (s.tapes 4).read.isSome)}

theorem sign_steps (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (hp : s.pc = 0) :
    PricedSteps (signProgram.next input tape) 3 s (signedState s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, signProgram, hp, signedState, BitRAMState.setRegister]

theorem sign_frame (s : BitRAMState) : Frame 0 s (signedState s) := by
  simp [Frame, signedState]
  intro i _ hi _
  simp [show i ≠ 23 by omega, show i ≠ 26 by omega, show i ≠ 27 by omega]

def code : Code := .seq bumpCode (.seq (.call (NormalizeWord.program 4)) (.call signProgram))

/-- Apply the computed Boolean increment and emit a canonical sign bit:
zero is always represented with a false sign. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (word : List Bool) (origin : ℤ) (negative flag : Bool)
    (hw : s.val.tapes 4 = BitTape.shifted word origin)
    (hs : s.val.registers 35 = negative) (hf : s.val.registers 36 = flag) :
    ∃ cost, ∃ t : Store, cost ≤ 40 * (word.length + 2) ∧
      Executes input tape code cost s t ∧
      t.val.tapes 4 = BitTape.shifted (addressValue word + flag.toNat).bits origin ∧
      t.val.registers 23 = (negative && decide (0 < addressValue word + flag.toNat)) ∧
      (∀ i, i ≠ 4 → t.val.tapes i = s.val.tapes i) ∧ Frame 5 s.val t.val := by
  obtain ⟨bumpCost, a, result, hbCost, hb, hl, hv, ha4, hat, haf⟩ :=
    bump input tape s word origin flag hw hf
  obtain ⟨normCost, normalized, hnCost, hn, hnp, hn4, _, hnf⟩ :=
    NormalizeWord.simulation 4 origin input tape result a.val a.property ha4
  let b : Store := Store.ofState normalized
  have heb : Executes input tape (.call (NormalizeWord.program 4)) (normCost + 1) a b :=
    Executes.call _ _ _ _ hn (by
      simp [NormalizeWord.program, hnp, ScanForward.program, TapeOps.trim,
        Rewind.program, BitRAMInstruction.relocate])
  let t : Store := Store.ofState (signedState b.val)
  have het : Executes input tape (.call signProgram) 4 b t :=
    Executes.call _ _ _ _ (sign_steps input tape b.val b.property) (by simp [signProgram, signedState])
  have hbf : Frame 5 a.val b.val := frame_of_normalize (by omega) hnf
  have hbSign : b.val.registers 35 = negative := hbf.sign.trans (haf.sign.trans hs)
  have hb4 : b.val.tapes 4 = BitTape.shifted (addressValue word + flag.toNat).bits origin := by
    simpa [b, Store.ofState, hv] using hn4
  refine ⟨bumpCost + ((normCost + 1) + 4), t, by omega, hb.seq (heb.seq het), ?_, ?_, ?_,
    (haf.trans hbf).trans ((sign_frame b.val).mono (by omega))⟩
  · exact hb4
  · simp [t, Store.ofState, signedState, hb4, hbSign, Decision.canonical_nonempty]
  · intro i hi
    exact (hnf.2.2.2.2.2.1 i hi).trans (hat i hi)

end Maxwell.Cost.SignedRound.Quotient
