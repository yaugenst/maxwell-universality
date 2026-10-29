import Maxwell.Cost.NormalizeCoefficient.Load
import Maxwell.Cost.NormalizeCoefficient.Cleanup
import Maxwell.Cost.NormalizeRatio

namespace Maxwell.Cost.NormalizeCoefficient

set_option maxHeartbeats 800000

open Structured RationalAccumulator

def code : Code := .seq (.atom (.bitAnd 35 23 23))
  (.seq loadCode (.seq NormalizeRatio.code cleanupCode))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 5 ≤ i → i ≠ 12 → i ≠ 13 → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → (i < 23 ∨ 29 < i) → i ≠ 35 → i ≠ 36 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi hj hk hl => (kt i hi hj hk hl).trans (ht i hi hj hk hl),
    fun i hi hj hk hl => (kg i hi hj hk hl).trans (hg i hi hj hk hl)⟩

theorem frame_of_parse {s t : BitRAMState} (h : ParseFrame s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi hj hk hl => ht i (by omega) hj hk hl,
    fun i hi hj _ _ => hg i hi (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_ratio {s t : BitRAMState} (h : NormalizeRatio.Frame s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi _ _ hl => ht i hi hl,
    fun i hi hj _ hl => hg i hi hj hl⟩

theorem normalized_values (q : Codec.RationalPair) (scaleNum scaleDen precision : ℕ) :
    NormalizeRatio.normalized (values q scaleNum scaleDen precision) (decide (q.numerator < 0)) =
      q.value / ((scaleNum : ℚ) / scaleDen) := by
  have hn : (if decide (q.numerator < 0) then -(q.numerator.natAbs : ℚ)
      else q.numerator.natAbs) = q.numerator := by
    by_cases h : q.numerator < 0
    · simp only [h, decide_true, ↓reduceIte]
      have he : -(q.numerator.natAbs : ℤ) = q.numerator := by
        rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]
      exact_mod_cast he
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (le_of_not_gt h))
  simp only [NormalizeRatio.normalized, values, Function.update_apply,
    show (30 : ℕ) ≠ 34 by omega, show (30 : ℕ) ≠ 33 by omega,
    show (30 : ℕ) ≠ 32 by omega, show (30 : ℕ) ≠ 31 by omega,
    show (31 : ℕ) ≠ 34 by omega, show (31 : ℕ) ≠ 33 by omega,
    show (31 : ℕ) ≠ 32 by omega, show (32 : ℕ) ≠ 34 by omega,
    show (32 : ℕ) ≠ 33 by omega, show (33 : ℕ) ≠ 34 by omega,
    ↓reduceIte, hn, Codec.RationalPair.value]

/-- Consume the actual parser words, copy the persistent scale and power,
round the normalized ratio, and clear every arithmetic bank operand. -/
theorem normalizes (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (values q scaleNum scaleDen precision i).bits.length ≤ B)
    (s : Store) (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0))
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ cost, ∃ t : Store, cost ≤ 110000 * (B + 2)^2 ∧ Executes input tape code cost s t ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision
        (q.value / ((scaleNum : ℚ) / scaleDen))).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ Frame s.val t.val := by
  let a : Store := Store.ofState (s.val.setRegister 35 (s.val.registers 23 && s.val.registers 23))
  have ha := Executes.bitAnd input tape s 35 23 23
  have haf : Frame s.val a.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, ?_⟩
    intro i _ _ hi _
    simp [a, Store.ofState, BitRAMState.setRegister, hi]
  have has : a.val.registers 35 = decide (q.numerator < 0) := by
    simp [a, Store.ofState, BitRAMState.setRegister, hsign]
  obtain ⟨b, hb, hbb, hbr, hb12, hb13, hbf⟩ := load input tape q scaleNum scaleDen precision
    a hbank hready hnum hden hscaleN hscaleD hpower
  have hb4 : Blank b.val 4 := blank_of_eq
    (hbf.2.2.2.2.2.1 4 (by omega) (by omega) (by omega) (Or.inl (by omega))) hfour
  have hbs : b.val.registers 35 = decide (q.numerator < 0) :=
    (hbf.2.2.2.2.2.2 35 (by omega) (by omega) (by omega) (by omega) (by omega)).trans has
  obtain ⟨rcost, r, hrCost, hr, hro, hrb, hrr, hrf⟩ := NormalizeRatio.normalizes input tape
    (values q scaleNum scaleDen precision) B precision (decide (q.numerator < 0)) hbits
    (by simpa [values] using q.denominator_pos) (by simpa [values] using hscaleNum)
    (by simpa [values] using hscaleDen) (by simp [values]) (by simp [values])
    (by simp [values]) b hbb hbr hb4 hbs
  obtain ⟨t, ht, htb, htr, htf⟩ := cleanup input tape (values q scaleNum scaleDen precision)
    r hrb hrr (by simp [values]) (by simp [values])
  let L := q.numerator.natAbs.bits.length + q.denominator.bits.length
  let K := scaleNum.bits.length + scaleDen.bits.length + (2^precision).bits.length
  refine ⟨2 + (21*L+15*K+95 + (rcost + (6*(L+K)+20))), t, ?_, ?_, ?_, htb, htr, ?_, ?_,
    ((haf.trans (frame_of_parse hbf)).trans (frame_of_ratio hrf)).trans
      (frame_of_parse (parseFrame_of_frame htf))⟩
  · have hb30 := hbits 30 (by omega) (by omega)
    have hb31 := hbits 31 (by omega) (by omega)
    have hb32 := hbits 32 (by omega) (by omega)
    have hb33 := hbits 33 (by omega) (by omega)
    have hb34 := hbits 34 (by omega) (by omega)
    simp only [values, Function.update_apply] at hb30 hb31 hb32 hb33 hb34
    norm_num at hb30 hb31 hb32 hb33 hb34
    dsimp [L, K]
    nlinarith
  · have he := ha.seq (hb.seq (hr.seq ht))
    simp only [values, Function.update_apply] at he
    norm_num at he
    convert he using 1 <;> first | rfl | (dsimp [L, K]; omega)
  · rw [normalized_values] at hro
    obtain ⟨origin, hout, hsg⟩ := hro
    exact ⟨origin, (htf.2.2.2.2.2.1 4 (by omega) (Or.inl (by omega))).trans hout,
      (htf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hsg⟩
  · exact (htf.2.2.2.2.2.1 12 (by omega) (Or.inl (by omega))).trans
      ((hrf.2.2.2.2.2.1 12 (by omega) (Or.inl (by omega))).trans hb12)
  · exact (htf.2.2.2.2.2.1 13 (by omega) (Or.inl (by omega))).trans
      ((hrf.2.2.2.2.2.1 13 (by omega) (Or.inl (by omega))).trans hb13)

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (values q scaleNum scaleDen precision i).bits.length ≤ B)
    (s : Store) (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0))
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (110000 * (B + 2)^2 + 1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (110000 * (B + 2)^2 + 1) s.val).instructions ≤
        110000 * (B + 2)^2 ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision
        (q.value / ((scaleNum : ℚ) / scaleDen))).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, ho, hb, hs, hn, hd, hf⟩ := normalizes input tape q scaleNum scaleDen
    precision B hscaleNum hscaleDen hbits s hbank hready hfour hnum hden hsign hscaleN hscaleD hpower
  have hr := he.compiled_run (110000 * (B + 2)^2 + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ho, hb, hs, hn, hd, hf⟩

end Maxwell.Cost.NormalizeCoefficient
