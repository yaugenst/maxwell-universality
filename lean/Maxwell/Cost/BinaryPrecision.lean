import Maxwell.Cost.WordLength
import Maxwell.Cost.DecoderConstants.Helpers
import Maxwell.Realization.BinaryPrecision

/-! Actual finite metadata generation from a stored canonical input-size
word. Only the promise exponents determine the literal program constants;
the input-size length is measured by the physical WordLength routine. -/

namespace Maxwell.Cost.BinaryPrecision
open Structured
open RationalAccumulator (Word Blank)

def work : Finset ℕ := {0, 1, 2, 3, 68, 70, 71, 72, 73}

structure Frame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  inputHead : t.inputHead = s.inputHead
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i ∉ changed, t.tapes i = s.tapes i

theorem Frame.trans {changed : Finset ℕ} {s t u : BitRAMState}
    (h : Frame changed s t) (k : Frame changed t u) : Frame changed s u :=
  ⟨k.address.trans h.address, k.inputHead.trans h.inputHead, k.memory.trans h.memory,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Frame.refl (changed : Finset ℕ) (s : BitRAMState) : Frame changed s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState} (h : Frame a s t)
    (hab : a ⊆ b) : Frame b s t :=
  ⟨h.address, h.inputHead, h.memory, h.randomCursor, h.output,
    fun i hi => h.tapes i (fun hh => hi (hab hh))⟩

def writeCode (target : ℕ) : List Bool → Code
  | [] => .skip
  | b :: rest => .seq (PowerOfTwo.appendBit target b) (writeCode target rest)

def literalCode (target n : ℕ) : Code :=
  .seq (writeCode target n.bits) (.call (Rewind.program target))

theorem write_executes (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits preceding : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shiftedEnd preceding origin) :
    ∃ t, Executes input tape (writeCode target bits) (6 * bits.length + 1) s t ∧
      t.val.tapes target = BitTape.shiftedEnd (preceding ++ bits) origin ∧
      Frame {target} s.val t.val := by
  induction bits generalizing preceding s with
  | nil => exact ⟨s, .skip s, by simpa using ht, Frame.refl _ _⟩
  | cons b bits ih =>
    let a := PowerOfTwo.appendState target b s
    have ha : a.val.tapes target = BitTape.shiftedEnd (preceding ++ [b]) origin :=
      PowerOfTwo.append_word target b s preceding origin ht
    obtain ⟨t, et, htt, ft⟩ := ih (preceding ++ [b]) a ha
    have fa : Frame {target} s.val a.val := by
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro i hi
      have hne : i ≠ target := by simpa using hi
      simp [a, PowerOfTwo.appendState, Store.ofState, hne]
    refine ⟨t, ?_, by simpa [List.append_assoc] using htt, fa.trans ft⟩
    convert (PowerOfTwo.append_executes target b input tape s).seq et using 1 <;>
      first | rfl | simp only [List.length_cons]; omega

/-- The fixed integer is expanded into literal writes during compilation,
and every write, move, rewind and return remains charged at execution. -/
theorem literal (target n : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Blank s.val target) :
    ∃ t, Executes input tape (literalCode target n) (10 * n.bits.length + 7) s t ∧
      Word t.val target n ∧ Frame {target} s.val t.val := by
  obtain ⟨origin, ho⟩ := hb
  obtain ⟨a, ea, ha, fa⟩ := write_executes target input tape n.bits [] origin s (by simpa using ho)
  have hw : a.val.tapes target = BitTape.shiftedEnd n.bits origin := by simpa using ha
  have hr := WordTransfer.rewind_shifted target origin input tape n.bits a.val a.property hw
  let t := Store.ofState (Rewind.finishAt target origin a.val)
  have er : Executes input tape (.call (Rewind.program target)) (4 * n.bits.length + 6) a t :=
    .call _ a _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  have ft : Frame {target} a.val t.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    have hne : i ≠ target := by simpa using hi
    simp [t, Store.ofState, Rewind.finishAt, hne]
  refine ⟨t, ?_, ⟨origin, hr.2⟩, fa.trans ft⟩
  convert ea.seq er using 1 <;> first | rfl | omega

def code (source k c : ℕ) : Code :=
  .seq (WordLength.code source 70)
    (.seq (literalCode 72 (k + c + 2))
      (.seq (literalCode 73 7)
        (.seq (DecoderTerm.multiplyCode 72 70)
          (.seq (DecoderConstants.addCode 73 70) (DecoderConstants.powerCode 70 71)))))

def program (source k c : ℕ) : BitRAM := (code source k c).compile

def precision (L k c : ℕ) : ℕ := 7 + (k + c + 2) * L

def costBound (L k c : ℕ) : ℕ := 2000 * ((k + c + 12) * (L + 1)) ^ 2

private theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  simpa only [WordLength.countBits_eq] using WordLength.countBits_length n

private theorem outside_work {i : ℕ} (hi : i ∉ work) :
    4 ≤ i ∧ i ≠ 68 ∧ i ≠ 70 ∧ i ≠ 71 ∧ i ≠ 72 ∧ i ≠ 73 := by
  simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  omega

private theorem frame_stored {target : ℕ} (ht : target ∈ work)
    {s t : BitRAMState} (h : StoredProduct.Frame target s t) : Frame work s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro i hi
  exact h.2.2.2.2.2.1 i (outside_work hi).1 (fun heq => hi (heq ▸ ht))

theorem executes_word (source k c : ℕ) (hsource : source ∉ work)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted word origin)
    (hblank : ∀ i ∈ work, Blank s.val i) :
    ∃ cost t, Executes input tape (code source k c) cost s t ∧
      cost ≤ costBound word.length k c ∧
      Word t.val 70 (precision word.length k c) ∧
      Word t.val 71 (2 ^ precision word.length k c) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 68 ∧
      t.val.tapes source = BitTape.shifted word origin ∧ Frame work s.val t.val := by
  obtain ⟨lengthOrigin, hlenBlank⟩ := hblank 70 (by simp [work])
  have hsource70 : source ≠ 70 := (outside_work hsource).2.2.1
  obtain ⟨lengthCost, a, ea, hLengthCost, haSource, haLength, haFrame⟩ :=
    WordLength.executes source 70 hsource70 input tape word origin lengthOrigin s hs hlenBlank
  have fa : Frame {70} s.val a.val := by
    refine ⟨haFrame.1, haFrame.2.1, haFrame.2.2.1, haFrame.2.2.2.1, haFrame.2.2.2.2.1, ?_⟩
    intro i hi
    have hi70 : i ≠ 70 := by simpa using hi
    by_cases his : i = source
    · subst i; exact haSource.trans hs.symm
    · exact haFrame.2.2.2.2.2.1 i his hi70
  have ha72 : Blank a.val 72 := RationalAccumulator.blank_of_eq (fa.tapes 72 (by simp))
    (hblank 72 (by simp [work]))
  obtain ⟨b, eb, hb72, fb⟩ := literal 72 (k + c + 2) input tape a ha72
  have hb73 : Blank b.val 73 := RationalAccumulator.blank_of_eq
    ((fb.tapes 73 (by simp)).trans (fa.tapes 73 (by simp))) (hblank 73 (by simp [work]))
  obtain ⟨d, ed, hd73, fd⟩ := literal 73 7 input tape b hb73
  have fdwork : Frame work s.val d.val :=
    ((fa.mono (by simp [work])).trans (fb.mono (by simp [work]))).trans (fd.mono (by simp [work]))
  have hd70 : Word d.val 70 word.length := ⟨lengthOrigin,
    (fd.tapes 70 (by simp)).trans ((fb.tapes 70 (by simp)).trans haLength)⟩
  have hd72 : Word d.val 72 (k + c + 2) :=
    RationalAccumulator.word_of_eq (fd.tapes 72 (by simp)) hb72
  have hdblank (i : ℕ) (hi : i < 4) : Blank d.val i :=
    RationalAccumulator.blank_of_eq
      ((fd.tapes i (by simp; omega)).trans ((fb.tapes i (by simp; omega)).trans
        (fa.tapes i (by simp; omega)))) (hblank i (by interval_cases i <;> simp [work]))
  obtain ⟨multiplyCost, e, hMultiplyCost, ee, he70, heblank, fe⟩ :=
    DecoderTerm.multiply 72 70 (by decide) (by decide) (by decide) input tape
      (k + c + 2) word.length d hd72 hd70 hdblank
  have he73 : Word e.val 73 7 := RationalAccumulator.word_of_eq
    (fe.2.2.2.2.2.1 73 (by decide) (by decide)) hd73
  obtain ⟨addCost, f, hAddCost, ef, hf70, hfblank, ff⟩ := DecoderConstants.add 73 70
    (by decide) (by decide) (by decide) input tape 7 ((k + c + 2) * word.length)
      e he73 he70 heblank
  have ffwork : Frame work s.val f.val :=
    (fdwork.trans (frame_stored (by simp [work]) fe)).trans (frame_stored (by simp [work]) ff)
  have fkeep (i : ℕ) (hi : 4 ≤ i) (h70 : i ≠ 70) (h72 : i ≠ 72) (h73 : i ≠ 73) :
      f.val.tapes i = s.val.tapes i :=
    (ff.2.2.2.2.2.1 i hi h70).trans ((fe.2.2.2.2.2.1 i hi h70).trans
      ((fd.tapes i (by simpa using h73)).trans ((fb.tapes i (by simpa using h72)).trans
        (fa.tapes i (by simpa using h70)))))
  obtain ⟨powerCost, t, hPowerCost, et, ht71, ht68, ft⟩ :=
    DecoderConstants.power 70 71 (by decide) (by decide) (by decide) input tape
      (precision word.length k c) f hf70
      (RationalAccumulator.blank_of_eq (fkeep 71 (by decide) (by decide) (by decide) (by decide))
        (hblank 71 (by simp [work])))
      (RationalAccumulator.blank_of_eq (fkeep 68 (by decide) (by decide) (by decide) (by decide))
        (hblank 68 (by simp [work])))
  have ftwork : Frame work f.val t.val := by
    refine ⟨ft.1, ft.2.1, ft.2.2.1, ft.2.2.2.1, ft.2.2.2.2.1, ?_⟩
    intro i hi
    have hout := outside_work hi
    exact ft.2.2.2.2.2.1 i hout.2.1 hout.2.2.2.1
  have fall := ffwork.trans ftwork
  refine ⟨_, t, ea.seq (eb.seq (ed.seq (ee.seq (ef.seq et)))), ?_,
    RationalAccumulator.word_of_eq (ft.2.2.2.2.2.1 70 (by decide) (by decide)) hf70,
    ht71, ?_, ht68, (fall.tapes source hsource).trans hs, fall⟩
  · let L := word.length
    let A := k + c + 2
    let B := (A + 10) * (L + 1)
    have hB : 12 ≤ B := by dsimp [B, A]; nlinarith
    have hL : L + 1 ≤ B := by dsimp [B, A]; nlinarith
    have hA : A ≤ B := by dsimp [B]; nlinarith
    have hAL : A + L + 3 ≤ B := by dsimp [B, A]; nlinarith
    have hP : A * L ≤ B := by dsimp [B]; nlinarith
    have hS : precision L k c + 1 ≤ B := by dsimp [precision, B, A]; nlinarith
    have hAbits := bits_length_le A
    have hLbits := bits_length_le L
    have hPbits := bits_length_le (A * L)
    have hSbits := bits_length_le (precision L k c)
    change powerCost ≤ (precision L k c + 1) * (13 * (precision L k c).bits.length + 25) +
      21 * (precision L k c).bits.length + 27 at hPowerCost
    have hseven : (7 : ℕ).bits.length = 3 := by decide
    have h1 : lengthCost ≤ 49 * B ^ 2 := by
      have hh : (L + 1)^2 ≤ B^2 := Nat.pow_le_pow_left hL 2
      change lengthCost ≤ 48 * (L + 1)^2 + 1 at hLengthCost
      nlinarith
    have h2 : 10 * A.bits.length + 7 + (10 * (7 : ℕ).bits.length + 7) ≤ 20 * B^2 := by
      rw [hseven]
      nlinarith
    have h3 : multiplyCost ≤ 600 * B^2 := by
      have hh : A.bits.length + L.bits.length + 3 ≤ B := by omega
      exact hMultiplyCost.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left hh 2))
    have h4 : addCost ≤ 200 * B^2 := by
      have hh : (7 : ℕ).bits.length + (A * L).bits.length + 4 ≤ B + 7 := by rw [hseven]; omega
      have hh' : B + 7 ≤ B^2 := by nlinarith
      exact hAddCost.trans (Nat.mul_le_mul_left 200 (hh.trans hh'))
    have h5 : powerCost ≤ 100 * B^2 := by
      have hh : powerCost ≤ B * (13 * B + 25) + 21 * B + 27 :=
        hPowerCost.trans (by gcongr <;> omega)
      nlinarith
    change _ ≤ 2000 * B^2
    change 10 * A.bits.length + 7 + (10 * (7 : ℕ).bits.length + 7) ≤ _ at h2
    nlinarith
  · intro i hi
    exact RationalAccumulator.blank_of_eq (ft.2.2.2.2.2.1 i (by omega) (by omega)) (hfblank i hi)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem executes (source m k c : ℕ) (hsource : source ∉ work)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Word s.val source m) (hblank : ∀ i ∈ work, Blank s.val i) :
    ∃ cost t, Executes input tape (code source k c) cost s t ∧
      cost ≤ costBound m.size k c ∧
      Word t.val 70 (Realization.binaryCoefficientPrecision m k c) ∧
      Word t.val 71 (2 ^ Realization.binaryCoefficientPrecision m k c) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 68 ∧ Frame work s.val t.val := by
  obtain ⟨origin, ho⟩ := hs
  obtain ⟨cost, t, he, hc, hs', hp, hb, h68, _, hf⟩ :=
    executes_word source k c hsource input tape m.bits origin s ho hblank
  refine ⟨cost, t, he, ?_, ?_, ?_, hb, h68, hf⟩
  · simpa only [Nat.size_eq_bits_len] using hc
  · simpa only [Nat.size_eq_bits_len, Realization.binaryCoefficientPrecision, precision] using hs'
  · simpa only [Nat.size_eq_bits_len, Realization.binaryCoefficientPrecision, precision] using hp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem run (source m k c : ℕ) (hsource : source ∉ work)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Word s.val source m) (hblank : ∀ i ∈ work, Blank s.val i) :
    ∃ t : BitRAMState,
      (runPriced ((program source k c).next input tape) (costBound m.size k c + 1) s.val).finished = some t ∧
      (runPriced ((program source k c).next input tape) (costBound m.size k c + 1) s.val).instructions ≤
        costBound m.size k c ∧
      Word t 70 (Realization.binaryCoefficientPrecision m k c) ∧
      Word t 71 (2 ^ Realization.binaryCoefficientPrecision m k c) ∧ Frame work s.val t := by
  obtain ⟨cost, t, he, hc, h70, h71, _, _, hf⟩ := executes source m k c hsource input tape s hs hblank
  obtain ⟨hfinished, hcost⟩ := he.compiled_run (costBound m.size k c + 1) (by omega)
  refine ⟨t.place (code source k c).size, hfinished, hcost.trans_le hc, h70, h71, ?_⟩
  exact ⟨hf.address, hf.inputHead, hf.memory, hf.randomCursor, hf.output, hf.tapes⟩

end Maxwell.Cost.BinaryPrecision
