import Maxwell.Cost.RationalNormalize.Pipeline

/-! A bounded finite Boolean/address machine for rational vector normalization.
The input and output arrays contain unreduced signed integer channels; the
common denominator is returned on tape 153. -/

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator CalibrationMatrix

theorem costBound_le (n B W p countLength : ℕ) (hc : countLength ≤ B) :
    costBound n B W p countLength ≤ 1300000*(n+1)*(B+2)^2 + scalarBudget W p := by
  have hs := Scale.costBound_le n B
  have hquad : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
  have hcount : (n+1)*(13*countLength+15) ≤ (n+1)*(13*B+15) := by gcongr
  have hprod := Nat.mul_le_mul_left (n+1) hquad
  unfold costBound normCost dotCost
  nlinarith

/-- Capped execution of one fixed compiled program returns the actual
array representation of the proved rational normalized vector. -/
theorem compiled_run {n : ℕ} (d : Data n n) (sd : Scale.Data n)
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
    ∃ t : Store, ∃ finalIndex : List Bool,
      (runPriced (code.compile.next input tape) (costBound n B W p normCount.length+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound n B W p normCount.length+1) s.val).instructions ≤
        costBound n B W p normCount.length ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Scale.Stored sd (Scale.filledWords sd words n) t.val ∧
      Word t.val 153 (outputDenominator (integerVector d) C D p) ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ i, (((Scale.channels (Scale.filledWords sd words n) 2 3).value i : ℤ) : ℚ) /
        (outputDenominator (integerVector d) C D p : ℚ) =
          Maxwell.Defect.RationalNormalize.vector (fun j => (integerVector d j : ℚ))
            ((C : ℚ)/D) p i) := by
  obtain ⟨steps, t, fi, hs, he, hfinal⟩ := executes d sd words B W C D p
    hpositive hnegative hsource hK hCpos hd hsd hn hpos hneg hBW hC hD hwp hwn
    input tape mi vi normCount scaleIndex scaleCount hmi hvi hml hvl hnc hsi hsc hsil hscl
    normOrigin scaleOrigin s h106 h108 hready hdata hindices h104 h37 h40 h126 h153
    hCword hDword hpword hswidth hsclock hsbases hsarrays
  have hrun := he.compiled_run (costBound n B W p normCount.length+1) (by omega)
  exact ⟨t, fi, hrun.1, hrun.2 ▸ hs, hfinal⟩

end Maxwell.Cost.RationalNormalize
