import Maxwell.Continuum.CalibrationStoredPairingData
import Maxwell.Cost.WordReplace

/-! Charged handoff from the final calibration arrays to a scalar pairing.
The matrix headers are repurposed only after the iteration has finished;
the literal arrays, vector headers, and denominator tapes survive. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 2200000

def setupCode (p q : Fin 12) : Code :=
  .seq (WordReplace.code (Horner.baseBank p) 110)
    (.seq (WordReplace.code (Horner.baseBank q) 111)
      (.call (WordTransfer.clone 107 106)))

def setupCost {n : ℕ} (a : Snapshot n) (p q : Fin 12) (count : List Bool) : ℕ :=
  6*a.data.matrixPositiveBase.length+15*(a.data.bases p).length+21+
    (6*a.data.matrixNegativeBase.length+15*(a.data.bases q).length+21+
      (15*count.length+17))

def SetupFrame (s t : BitRAMState) : Prop :=
  t.memory=s.memory ∧ t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧
    t.output=s.output ∧ ∀ i, i≠106 → i≠110 → i≠111 → t.tapes i=s.tapes i

theorem setup {n B : ℕ} (a : Snapshot n) (p q : Fin 12) (count : List Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : a.Ready count B s.val) :
    ∃ t : Store, ∃ vi : List Bool, ∃ origin : ℤ,
      Executes input tape (setupCode p q) (setupCost a p q count) s t ∧
      CalibrationMatrix.Ready t.val (dotValues 0 0) ∧
      CalibrationMatrix.Stored (data a p q) t.val ∧ Indices t.val [] vi ∧
      addressValue vi=0 ∧ vi.length≤B ∧
      t.val.tapes 106=BitTape.shifted count origin ∧ SetupFrame s.val t.val := by
  have hp := Horner.baseBank_bounds p
  have hq := Horner.baseBank_bounds q
  obtain ⟨b,eb,wb,fb⟩ := WordReplace.executes (Horner.baseBank p) 110 (by omega)
    input tape (a.data.bases p) a.data.matrixPositiveBase s (ha.2.1.bases p)
      ha.2.1.matrixPositiveBase
  obtain ⟨c,ec,wc,fc⟩ := WordReplace.executes (Horner.baseBank q) 111 (by omega)
    input tape (a.data.bases q) a.data.matrixNegativeBase b
      (BankArray.word_of_eq (fb.2.2.2.2.2.1 _ (by omega)) (ha.2.1.bases q))
      (BankArray.word_of_eq (fb.2.2.2.2.2.1 111 (by omega)) ha.2.1.matrixNegativeBase)
  have keepC (i : ℕ) (h110 : i≠110) (h111 : i≠111) :
      c.val.tapes i=s.val.tapes i :=
    (fc.2.2.2.2.2.1 i h111).trans (fb.2.2.2.2.2.1 i h110)
  obtain ⟨vi,hvi,hvl,cal,indices,_,countWord,blank,_,_,_⟩ := ha.1
  obtain ⟨co,countWord⟩ := countWord
  obtain ⟨origin,blank⟩ := blank
  obtain ⟨t,et,tt,ft⟩ := WordCall.clone 107 106 (by omega) input tape count co origin c
    ((keepC 107 (by omega) (by omega)).trans countWord)
    ((keepC 106 (by omega) (by omega)).trans blank)
  have keepT (i : ℕ) (hi : i≠106) : t.val.tapes i=c.val.tapes i := by simp [tt,hi]
  have keep (i : ℕ) (h106 : i≠106) (h110 : i≠110) (h111 : i≠111) :
      t.val.tapes i=s.val.tapes i := (keepT i h106).trans (keepC i h110 h111)
  have memory : t.val.memory=s.val.memory := ft.2.2.1.trans (fc.2.2.1.trans fb.2.2.1)
  refine ⟨t,vi,origin,eb.seq (ec.seq et),
    cal.of_tapes (fun i hi => keep i (by omega) (by omega) (by omega)),
    ⟨BankArray.word_of_eq (keep 100 (by omega) (by omega) (by omega)) ha.2.1.width,
      BankArray.word_of_eq (keep 101 (by omega) (by omega) (by omega)) ha.2.1.clock,
      BankArray.word_of_eq ((keepT 110 (by omega)).trans (fc.2.2.2.2.2.1 110 (by omega))) wb,
      BankArray.word_of_eq (keepT 111 (by omega)) wc,
      BankArray.word_of_eq (keep 112 (by omega) (by omega) (by omega)) ha.2.2.inputPositive,
      BankArray.word_of_eq (keep 113 (by omega) (by omega) (by omega)) ha.2.2.inputNegative,
      by simpa only [memory,data] using ha.2.1.arrays p,
      by simpa only [memory,data] using ha.2.1.arrays q,
      by simpa only [memory,data] using ha.2.1.arrays 10,
      by simpa only [memory,data] using ha.2.1.arrays 11⟩,
    ⟨BankArray.word_of_eq (keep 102 (by omega) (by omega) (by omega)) indices.1,
      BankArray.word_of_eq (keep 103 (by omega) (by omega) (by omega)) indices.2⟩,
    hvi,hvl,by simp [tt],memory,
    ft.2.1.trans (fc.2.1.trans fb.2.1),
    ft.2.2.2.1.trans (fc.2.2.2.1.trans fb.2.2.2.1),
    ft.2.2.2.2.1.trans (fc.2.2.2.2.1.trans fb.2.2.2.2.1),keep⟩

theorem setupCost_le {n B : ℕ} (a : Snapshot n) (p q : Fin 12) (count : List Bool)
    (hs : a.data.Sized B) (hc : count.length≤B) : setupCost a p q count≤57*B+59 := by
  have hp := hs.2.2.2.2.1 p
  have hq := hs.2.2.2.2.1 q
  have hmp := hs.2.2.1
  have hmn := hs.2.2.2.1
  unfold setupCost
  omega

#print axioms setup

end Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing
