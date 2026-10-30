import Maxwell.Continuum.CalibrationBufferCrossData
import Maxwell.Continuum.CalibrationStoredPairingSetup

/-! The previous and current power arrays are exposed to the actual dot
routine by two charged descriptor copies. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferCross

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000

def setupCode : Code := .seq (WordReplace.code 114 110)
  (.seq (WordReplace.code 115 111) (.call (WordTransfer.clone 107 106)))

def setupCost {n : ℕ} (b : Buffers n) (count : List Bool) : ℕ :=
  6*b.data.matrixPositiveBase.length+15*b.output.positiveBase.length+21+
    (6*b.data.matrixNegativeBase.length+15*b.output.negativeBase.length+21+
      (15*count.length+17))

theorem setup {n B : ℕ} (b : Buffers n) (count : List Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hb : b.Ready count B s.val) :
    ∃ t : Store, ∃ vi : List Bool, ∃ origin : ℤ,
      Executes input tape setupCode (setupCost b count) s t ∧
      CalibrationMatrix.Ready t.val (dotValues 0 0) ∧
      CalibrationMatrix.Stored (data b) t.val ∧ Indices t.val [] vi ∧
      addressValue vi=0 ∧ vi.length≤B ∧
      t.val.tapes 106=BitTape.shifted count origin ∧
      NeumannMachine.StoredPairing.SetupFrame s.val t.val := by
  obtain ⟨vi,hvi,hvl,cal,stored,indices,out,countWord,blank,_,_,_⟩ := hb
  obtain ⟨u,eu,wu,fu⟩ := WordReplace.executes 114 110 (by decide) input tape
    b.output.positiveBase b.data.matrixPositiveBase s out.positiveBase stored.matrixPositiveBase
  obtain ⟨v,ev,wv,fv⟩ := WordReplace.executes 115 111 (by decide) input tape
    b.output.negativeBase b.data.matrixNegativeBase u
    (BankArray.word_of_eq (fu.2.2.2.2.2.1 115 (by decide)) out.negativeBase)
    (BankArray.word_of_eq (fu.2.2.2.2.2.1 111 (by decide)) stored.matrixNegativeBase)
  have keepV (i : ℕ) (h110 : i≠110) (h111 : i≠111) : v.val.tapes i=s.val.tapes i :=
    (fv.2.2.2.2.2.1 i h111).trans (fu.2.2.2.2.2.1 i h110)
  obtain ⟨co,countWord⟩ := countWord
  obtain ⟨origin,blank⟩ := blank
  obtain ⟨t,et,tt,ft⟩ := WordCall.clone 107 106 (by decide) input tape count co origin v
    ((keepV 107 (by decide) (by decide)).trans countWord)
    ((keepV 106 (by decide) (by decide)).trans blank)
  have keepT (i : ℕ) (hi : i≠106) : t.val.tapes i=v.val.tapes i := by simp [tt,hi]
  have keep (i : ℕ) (h106 : i≠106) (h110 : i≠110) (h111 : i≠111) : t.val.tapes i=s.val.tapes i :=
    (keepT i h106).trans (keepV i h110 h111)
  have memory : t.val.memory=s.val.memory := ft.2.2.1.trans (fv.2.2.1.trans fu.2.2.1)
  refine ⟨t,vi,origin,eu.seq (ev.seq et),
    cal.of_tapes (fun i hi => keep i (by omega) (by omega) (by omega)),
    ⟨BankArray.word_of_eq (keep 100 (by decide) (by decide) (by decide)) stored.width,
      BankArray.word_of_eq (keep 101 (by decide) (by decide) (by decide)) stored.clock,
      BankArray.word_of_eq ((keepT 110 (by decide)).trans (fv.2.2.2.2.2.1 110 (by decide))) wu,
      BankArray.word_of_eq (keepT 111 (by decide)) wv,
      BankArray.word_of_eq (keep 112 (by decide) (by decide) (by decide)) stored.vectorPositiveBase,
      BankArray.word_of_eq (keep 113 (by decide) (by decide) (by decide)) stored.vectorNegativeBase,
      by simpa only [memory,data] using out.positive,
      by simpa only [memory,data] using out.negative,
      by simpa only [memory,data] using stored.vectorPositive,
      by simpa only [memory,data] using stored.vectorNegative⟩,
    ⟨BankArray.word_of_eq (keep 102 (by decide) (by decide) (by decide)) indices.1,
      BankArray.word_of_eq (keep 103 (by decide) (by decide) (by decide)) indices.2⟩,
    hvi,hvl,by simp [tt],memory,
    ft.2.1.trans (fv.2.1.trans fu.2.1),
    ft.2.2.2.1.trans (fv.2.2.2.1.trans fu.2.2.2.1),
    ft.2.2.2.2.1.trans (fv.2.2.2.2.1.trans fu.2.2.2.2.1),keep⟩

theorem setupCost_le {n B : ℕ} (b : Buffers n) (count : List Bool)
    (hs : b.Sized B) (hc : count.length≤B) : setupCost b count≤57*B+59 := by
  obtain ⟨⟨_,_,hmp,hmn,_,_⟩,hop,hon⟩ := hs
  unfold setupCost
  omega

#print axioms setup

end Maxwell.Continuum.Calibration.PowerMachine.BufferCross
