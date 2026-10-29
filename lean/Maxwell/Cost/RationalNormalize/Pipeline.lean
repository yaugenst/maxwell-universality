import Maxwell.Cost.RationalNormalize.Norm
import Maxwell.Cost.RationalNormalize.Scalar
import Maxwell.Cost.RationalNormalize.Meaning

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator CalibrationMatrix

def code : Code := .seq normCode (.seq scalarCode Scale.code)

def costBound (n B W p countLength : ℕ) : ℕ :=
  normCost n B countLength + scalarBudget W p + Scale.costBound n B

theorem integerNormSq_width {n : ℕ} (d : Data n n)
    (hp : d.matrixPositive = d.vectorPositive) (hn : d.matrixNegative = d.vectorNegative)
    (B : ℕ) (hpos : (normPositive d).bits.length ≤ B) (hneg : (normNegative d).bits.length ≤ B) :
    (Maxwell.Defect.integerNormSq (integerVector d)).bits.length ≤ B+1 := by
  rw [← self_dot_magnitude d hp hn]
  have h := IntegerNormSquare.magnitude_bits_length_le (normPositive d) (normNegative d)
  omega

theorem normValues_eq {n : ℕ} (d : Data n n) : normValues d =
    inputBank (normPositive d) (normNegative d) (Maxwell.Defect.integerNormSq (integerVector d)) := by
  funext i
  by_cases h30 : i = 30
  · subst i; simp [normValues, dotValues, inputBank]
  by_cases h31 : i = 31
  · subst i; simp [normValues, dotValues, inputBank]
  by_cases h34 : i = 34
  · subst i; simp [normValues, dotValues, inputBank]
  simp [normValues, dotValues, inputBank, h30, h31, h34]

/-- One finite Boolean/address program computes the normalized rational
vector from the stored integer channels. The square norm, square root,
common denominator, and every coordinate product are all executed. -/
theorem executes {n : ℕ} (d : Data n n) (sd : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) (B W C D p : ℕ)
    (hpositive : d.matrixPositive = d.vectorPositive)
    (hnegative : d.matrixNegative = d.vectorNegative)
    (hsource : (Scale.channels words 0 1).value = integerVector d)
    (hK : sd.K = D*2^p) (hCpos : 0 < C)
    (hd : d.Sized B) (hsd : sd.Sized B) (hn : n < 2^B)
    (hpos : (normPositive d).bits.length ≤ B) (hneg : (normNegative d).bits.length ≤ B)
    (hBW : B+1 ≤ W) (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W)
    (hwp : ∀ i, (Scale.positive sd words i).bits.length ≤ addressValue sd.width)
    (hwn : ∀ i, (Scale.negative sd words i).bits.length ≤ addressValue sd.width)
    (input : List Bool) (tape : ℕ → Bool)
    (mi vi normCount scaleIndex scaleCount : List Bool)
    (hmi : addressValue mi = 0) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hnc : addressValue normCount = n)
    (hsi : addressValue scaleIndex = 0) (hsc : addressValue scaleCount = n)
    (hsil : scaleIndex.length ≤ B) (hscl : scaleCount.length ≤ B)
    (normOrigin scaleOrigin : ℤ) (s : Store)
    (h106 : s.val.tapes 106 = BitTape.shifted normCount normOrigin)
    (h108 : s.val.tapes 108 = BitTape.shifted scaleCount scaleOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val)
    (hindices : Indices s.val mi vi) (h104 : BankArray.Word s.val 104 scaleIndex)
    (h37 : Blank s.val 37) (h40 : Blank s.val 40)
    (h126 : Blank s.val 126) (h153 : Blank s.val 153)
    (hCword : Word s.val 150 C) (hDword : Word s.val 151 D) (hpword : Word s.val 152 p)
    (hswidth : BankArray.Word s.val 100 sd.width) (hsclock : BankArray.Word s.val 101 sd.clock)
    (hsbases : ∀ i, BankArray.Word s.val (Scale.baseBank i) (sd.bases i))
    (hsarrays : ∀ i, BitArray.Represents s.val.memory (addressValue (sd.bases i))
      (addressValue sd.width) (words i)) :
    ∃ steps, ∃ t : Store, ∃ finalIndex : List Bool,
      steps ≤ costBound n B W p normCount.length ∧ Executes input tape code steps s t ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Scale.Stored sd (Scale.filledWords sd words n) t.val ∧
      Word t.val 153 (outputDenominator (integerVector d) C D p) ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ i, (((Scale.channels (Scale.filledWords sd words n) 2 3).value i : ℤ) : ℚ) /
        (outputDenominator (integerVector d) C D p : ℚ) =
          Maxwell.Defect.RationalNormalize.vector (fun j => (integerVector d j : ℚ))
            ((C : ℚ)/D) p i) := by
  obtain ⟨c1, a, fm, fv, hc1, e1, _, _, _, _, _, _, r1, _, f1⟩ :=
    norm_executes d B hpositive hnegative hd hn hpos hneg input tape mi vi normCount
      hmi hvi hml hvl hnc normOrigin s h106 hready hdata hindices
  have keep1 (i : ℕ) (hi : 37 ≤ i) (h102 : i ≠ 102) (h103 : i ≠ 103) (h106 : i ≠ 106) :
      a.val.tapes i = s.val.tapes i :=
    f1.2.2.2.2.1 i (by omega) (by omega) h102 h103 h106
  have hA := (integerNormSq_width d hpositive hnegative B hpos hneg).trans hBW
  obtain ⟨c2, b, hc2, e2, hKword, hHword, b2, r2, _, f2⟩ := scalar_executes input tape
    (normPositive d) (normNegative d) (Maxwell.Defect.integerNormSq (integerVector d))
    C D W p (by omega) (by omega) hA hC hD a
    (by simpa only [normValues_eq] using r1.1) r1.arithmetic
    (blank_of_eq (keep1 40 (by decide) (by decide) (by decide) (by decide)) h40)
    (blank_of_eq (keep1 126 (by decide) (by decide) (by decide) (by decide)) h126)
    (blank_of_eq (keep1 153 (by decide) (by decide) (by decide) (by decide)) h153)
    (word_of_eq (keep1 150 (by decide) (by decide) (by decide) (by decide)) hCword)
    (word_of_eq (keep1 151 (by decide) (by decide) (by decide) (by decide)) hDword)
    (word_of_eq (keep1 152 (by decide) (by decide) (by decide) (by decide)) hpword)
  have keep (i : ℕ) (hi : 37 ≤ i) (h40 : i ≠ 40) (h102 : i ≠ 102)
      (h103 : i ≠ 103) (h106 : i ≠ 106) (h126 : i ≠ 126) (h153 : i ≠ 153) :
      b.val.tapes i = s.val.tapes i :=
    (f2.2.2.2.2.2.1 i (by omega) h40 h126 h153).trans (keep1 i hi h102 h103 h106)
  have hbmem : b.val.memory = s.val.memory := f2.2.2.1.trans f1.1
  have hbdata : Scale.Stored sd words b.val := by
    refine ⟨BankArray.word_of_eq (keep 100 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) hswidth,
      BankArray.word_of_eq (keep 101 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) hsclock,
      ?_, by simpa only [hK] using hKword, ?_⟩
    · intro i
      have hi : Scale.baseBank i = 120 ∨ Scale.baseBank i = 121 ∨
          Scale.baseBank i = 128 ∨ Scale.baseBank i = 129 := by
        fin_cases i <;> simp [Scale.baseBank]
      exact BankArray.word_of_eq (keep _ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)) (hsbases i)
    · intro i
      simpa only [hbmem] using hsarrays i
  have hbready : Ready b.val (dotValues 0 0) := by
    have hz : dotValues 0 0 = (fun _ => 0) := by funext i; simp [dotValues]
    rw [hz]
    exact ready_of_scalar r1 b2 r2 f2
  obtain ⟨c3, t, fi, hc3, e3, hfi, hfil, hti, htd, htr, ht37, ht108, _, htf, _⟩ :=
    Scale.executes sd words B hsd hn hwp hwn input tape scaleIndex scaleCount hsi hsc
      hsil hscl scaleOrigin b hbready hbdata
      (BankArray.word_of_eq (keep 104 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) h104)
      (blank_of_eq (keep 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) h37)
      ((keep 108 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans h108)
  refine ⟨c1+(c2+c3), t, fi, by unfold costBound; omega,
    e1.seq (e2.seq e3), hfi, hfil, hti, htd, ?_, htr, ht37, ht108,
    scaled_output_eq sd words (integerVector d) C D p hCpos hK hsource hwp hwn⟩
  exact word_of_eq (htf.2.2.2.1 153 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) hHword

end Maxwell.Cost.RationalNormalize
