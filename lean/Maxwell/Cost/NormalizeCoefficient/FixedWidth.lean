import Maxwell.Cost.NormalizeCoefficient.Correctness
import Maxwell.Cost.NormalizeCoefficient.PadReverse.Correctness
import Maxwell.Cost.NormalizeCoefficient.Bits

namespace Maxwell.Cost.NormalizeCoefficient

open Structured RationalAccumulator

def fixedWidthCode : Code := .seq code PadReverse.code

def FixedFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 5 ≤ i → i ≠ 12 → i ≠ 13 → i ≠ 83 → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → (i < 23 ∨ 29 < i) → i ≠ 35 → i ≠ 36 → t.registers i = s.registers i)

theorem fixed_frame {s r t : BitRAMState} (h : Frame s r) (k : PadReverse.Frame r t) :
    FixedFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi hj hk hl hm => (kt i (by omega) hl).trans (ht i hi hj hk hm),
    fun i hi hj hk hl => (kg i (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans (hg i hi hj hk hl)⟩

/-- The emitted word includes every leading zero and is most-significant
bit first. The rounded zero has false sign, independently of the input sign. -/
def FixedOutput (s : BitRAMState) (precision : ℕ) (z : ℤ) : Prop :=
  ∃ origin, s.tapes 83 = BitTape.shifted (Logical.Horner.encode precision z.natAbs) origin ∧
    s.registers 23 = decide (z < 0)

theorem fixed_width (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (values q scaleNum scaleDen precision i).bits.length ≤ B)
    (hsmall : (Logical.Rounding.nearest precision
      (q.value / ((scaleNum : ℚ) / scaleDen))).numerator.natAbs < 2^precision)
    (s : Store) (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4) (htarget : Blank s.val 83)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0))
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ cost, ∃ t : Store, cost ≤ 120000 * (B + 2)^2 ∧ Executes input tape fixedWidthCode cost s t ∧
      FixedOutput t.val precision (Logical.Rounding.nearest precision
        (q.value / ((scaleNum : ℚ) / scaleDen))).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧ Blank t.val 4 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ FixedFrame s.val t.val := by
  obtain ⟨cost, r, hc, he, ho, hb, hs, h12, h13, hf⟩ := normalizes input tape q scaleNum scaleDen
    precision B hscaleNum hscaleDen hbits s hbank hready hfour hnum hden hsign hscaleN hscaleD hpower
  let z := (Logical.Rounding.nearest precision (q.value / ((scaleNum : ℚ) / scaleDen))).numerator
  obtain ⟨origin, hout, hsg⟩ := ho
  have hwidth : z.natAbs.bits.length ≤ precision := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hsmall
  have hp := word_of_eq (hf.2.2.2.2.2.1 82 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) hpower
  have ht := blank_of_eq (hf.2.2.2.2.2.1 83 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) htarget
  obtain ⟨t, hte, ht4, ht83, htf⟩ := PadReverse.executes input tape precision z.natAbs
    hwidth r ⟨origin, hout⟩ hp ht
  refine ⟨cost+(15*precision+10), t, ?_, he.seq hte, ?_, ?_, ?_, ht4, ?_, ?_, fixed_frame hf htf⟩
  · have hprec := hbits 34 (by omega) (by omega)
    simp [values, PowerOfTwo.power_bits] at hprec
    nlinarith
  · obtain ⟨targetOrigin, hto⟩ := ht83
    rw [PadReverse.padded_reverse_eq_encode z.natAbs precision hsmall] at hto
    exact ⟨targetOrigin, hto, (htf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans hsg⟩
  · intro i hi hi'
    exact word_of_eq (htf.2.2.2.2.2.1 i (by omega) (by omega)) (hb i hi hi')
  · exact ⟨blank_of_eq (htf.2.2.2.2.2.1 0 (by omega) (by omega)) hs.1,
      word_of_eq (htf.2.2.2.2.2.1 1 (by omega) (by omega)) hs.2.1,
      blank_of_eq (htf.2.2.2.2.2.1 2 (by omega) (by omega)) hs.2.2.1,
      blank_of_eq (htf.2.2.2.2.2.1 3 (by omega) (by omega)) hs.2.2.2⟩
  · exact (htf.2.2.2.2.2.1 12 (by omega) (by omega)).trans h12
  · exact (htf.2.2.2.2.2.1 13 (by omega) (by omega)).trans h13

theorem fixed_width_compiled_run (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (values q scaleNum scaleDen precision i).bits.length ≤ B)
    (hsmall : (Logical.Rounding.nearest precision
      (q.value / ((scaleNum : ℚ) / scaleDen))).numerator.natAbs < 2^precision)
    (s : Store) (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4) (htarget : Blank s.val 83)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0))
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ t : Store,
      (runPriced (fixedWidthCode.compile.next input tape) (120000 * (B + 2)^2 + 1) s.val).finished =
        some (t.place fixedWidthCode.size) ∧
      (runPriced (fixedWidthCode.compile.next input tape) (120000 * (B + 2)^2 + 1) s.val).instructions ≤
        120000 * (B + 2)^2 ∧
      FixedOutput t.val precision (Logical.Rounding.nearest precision
        (q.value / ((scaleNum : ℚ) / scaleDen))).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧ Blank t.val 4 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ FixedFrame s.val t.val := by
  obtain ⟨cost, t, hc, he, ho, hb, hs, h4, hn, hd, hf⟩ := fixed_width input tape q scaleNum scaleDen
    precision B hscaleNum hscaleDen hbits hsmall s hbank hready hfour htarget hnum hden hsign
    hscaleN hscaleD hpower
  have hr := he.compiled_run (120000 * (B + 2)^2 + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ho, hb, hs, h4, hn, hd, hf⟩

end Maxwell.Cost.NormalizeCoefficient
