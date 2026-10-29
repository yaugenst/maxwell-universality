import Maxwell.Cost.RationalNormalize.Sqrt
import Maxwell.Cost.RationalNormalize.Factors
import Maxwell.Cost.RationalNormalize.Export

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator
open Maxwell.Defect.DyadicSqrt.Integer

def scalarCode : Code := .seq sqrtCode (.seq factorsCode exportCode)

def scalarBudget (W p : ℕ) : ℕ := sqrtBudget W p + 3000*(W+p+4)^2 + 100*(3*W+2*p+2)

def ScalarFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (4 ≤ i ∧ i < 30 ∨ 37 ≤ i) → i ≠ 40 → i ≠ 126 → i ≠ 153 →
    t.tapes i = s.tapes i) ∧
  (∀ i, 36 ≤ i → t.registers i = s.registers i)

theorem factors_width (A C D W p : ℕ)
    (hA : A.bits.length ≤ W) (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W) :
    DyadicSqrt.Width
      (factorsBank ((A*D^2)*4^p) (C^2) (upperNumerator A C D p) p C D) (3*W+2*p+1) := by
  have hDD := bits_mul_le D D
  have hADD := bits_mul_le A (D*D)
  have hCC := bits_mul_le C C
  have hscale := scaledNumerator_bits_length_le (A*D^2) p
  have hm : (upperNumerator A C D p).bits.length ≤ p+1 :=
    upperNum_bits_length_le (A*D^2) (C^2) p
  have hCm := bits_mul_le C (upperNumerator A C D p)
  have hDp := bits_mul_le D (2^p)
  have hpow : (2^p).bits.length = p+1 := by rw [Nat.size_eq_bits_len, Nat.size_pow]
  have hbig : ((A*D^2)*4^p).bits.length ≤ 3*W+2*p+1 := by
    simpa only [pow_two] using (show ((A*(D*D))*4^p).bits.length ≤ 3*W+2*p+1 by
      simp only [pow_two] at hscale
      omega)
  have hCsq : (C^2).bits.length ≤ 2*W := by
    simpa only [pow_two] using (show (C*C).bits.length ≤ 2*W by omega)
  intro i hi hi'
  interval_cases i <;> simp [factorsBank, DyadicSqrt.bank] <;> omega

/-- The complete scalar normalization phase reads C, D and precision from
stored input words and emits K=D*2^p and H=C*m, with an empty arithmetic bank. -/
theorem scalar_executes (input : List Bool) (tape : ℕ → Bool)
    (positive negative A C D W p : ℕ)
    (hp : positive.bits.length ≤ W) (hn : negative.bits.length ≤ W)
    (hA : A.bits.length ≤ W) (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W)
    (s : Store) (hbank : Bank s.val (inputBank positive negative A))
    (hready : Scratch s.val 0) (h40 : Blank s.val 40)
    (h126 : Blank s.val 126) (h153 : Blank s.val 153)
    (hCword : Word s.val 150 C) (hDword : Word s.val 151 D) (hpword : Word s.val 152 p) :
    ∃ cost, ∃ t : Store, cost ≤ scalarBudget W p ∧ Executes input tape scalarCode cost s t ∧
      Word t.val 126 (D*2^p) ∧ Word t.val 153 (C*upperNumerator A C D p) ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧ Blank t.val 40 ∧ ScalarFrame s.val t.val := by
  obtain ⟨c1, a, hc1, e1, b1, r1, h140, f1⟩ := sqrt_executes input tape
    positive negative A C D W p hp hn hA hC hD s hbank hready h40 hCword hDword hpword
  have haC := word_of_eq (f1.2.2.2.2.2.1 150 (by decide)) hCword
  have haD := word_of_eq (f1.2.2.2.2.2.1 151 (by decide)) hDword
  have hm : (upperNumerator A C D p).bits.length ≤ p+1 :=
    upperNum_bits_length_le (A*D^2) (C^2) p
  obtain ⟨c2, b, hc2, e2, b2, r2, f2⟩ := factors input tape ((A*D^2)*4^p) (C^2)
    (upperNumerator A C D p) p C D W hC hD hm a b1 r1 haC haD
  have f12 := f1.trans f2.toLoop
  obtain ⟨c3, t, hc3, e3, hK, hH, b3, r3, f3⟩ := export_executes input tape
    (factorsBank ((A*D^2)*4^p) (C^2) (upperNumerator A C D p) p C D) (3*W+2*p+1)
    (factors_width A C D W p hA hC hD) b b2 r2
    (blank_of_eq (f12.2.2.2.2.2.1 126 (by decide)) h126)
    (blank_of_eq (f12.2.2.2.2.2.1 153 (by decide)) h153)
  refine ⟨c1+(c2+c3), t, by unfold scalarBudget; omega, e1.seq (e2.seq e3),
    by simpa [factorsBank, DyadicSqrt.bank] using hK,
    by simpa [factorsBank, DyadicSqrt.bank] using hH, b3, r3, ?_, ?_⟩
  · exact blank_of_eq (f3.2.2.2.2.2.1 40 (by decide) (by decide) (by decide) (by decide))
      (blank_of_eq (f2.2.2.2.2.2.1 40 (by decide)) h140)
  · refine ⟨f3.1.trans f12.1, f3.2.1.trans f12.2.1, f3.2.2.1.trans f12.2.2.1,
      f3.2.2.2.1.trans f12.2.2.2.1, f3.2.2.2.2.1.trans f12.2.2.2.2.1, ?_,
      fun i hi => (f3.2.2.2.2.2.2 i hi).trans (f12.2.2.2.2.2.2 i hi)⟩
    intro i hi h40 h126 h153
    exact (f3.2.2.2.2.2.1 i (by omega) (by omega) h126 h153).trans
      (f12.2.2.2.2.2.1 i (by omega))

theorem ready_of_scalar {s t : BitRAMState} {v w : ℕ → ℕ}
    (h : CalibrationMatrix.Ready s v) (hb : Bank t w) (hs : Scratch t 0)
    (hf : ScalarFrame s t) : CalibrationMatrix.Ready t w := by
  have keep (i : ℕ) (hi : i < 10) (hi' : 4 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.2.1 i (by omega) (by omega) (by omega) (by omega)
  exact ⟨hb, ⟨hs.1, (zero_word_iff_blank t 1).mp hs.2.1, hs.2.2.1, hs.2.2.2,
    blank_of_eq (keep 5 (by omega) (by omega)) h.2.1.2.2.2.2.1,
    blank_of_eq (keep 6 (by omega) (by omega)) h.2.1.2.2.2.2.2.1,
    blank_of_eq (keep 8 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.1,
    blank_of_eq (keep 9 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.2⟩,
    blank_of_eq (keep 7 (by omega) (by omega)) h.2.2⟩

end Maxwell.Cost.RationalNormalize
