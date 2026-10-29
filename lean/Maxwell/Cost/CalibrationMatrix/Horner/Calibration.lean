import Maxwell.Cost.CalibrationMatrix.Horner.OutputState

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 1500000

def calibrationCode (l : Denominator.Layout) : Code :=
  .seq inverseCode (.seq (Denominator.code l) pairingCode)

def calibrationCost (N n B : ℕ) : ℕ := inverseCost N n B+Denominator.costCap N B+pairingCost n B

theorem calibrationCost_le (N n B : ℕ) :
    calibrationCost N n B ≤ 6000000*(N+1)*(n+1)^2*(B+2)^2 := by
  have hi := inverseCost_le N n B
  have hd := Denominator.costCap_le N B
  have hp := pairingCost_le n B
  dsimp [calibrationCost]
  nlinarith only [hi,hd,hp,Nat.zero_le
    ((1000000*N*n^2+2000000*N*n+600000*N+1000000*n^2+1450000*n+50000)*(B+2)^2)]

/-- The complete prepared-array calibration program: exact Horner inverse,
actual denominator power construction, actual descriptor/counter setup,
and exact rational scalar serialization. All three stages use fixed finite
instruction syntax; the mathematical recurrence appears only in the result. -/
theorem calibration_executes {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S U V : ℕ)
    (source : Channels n) (r : PairingRow n) (l : Denominator.Layout)
    (hdecode : a.Decodes A (D^2) S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (h1 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (horner A (D^2) S source k).2))
    (h2 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (matvec A (horner A (D^2) S source k).2)))
    (hw : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A (D^2) S source (k+1)).1)
    (hx : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A (D^2) S source (k+1)).2)
    (hprod : FitsWidth (addressValue a.data.width) (matvec A (horner A (D^2) S source N).2))
    (hscale : FitsWidth (addressValue a.data.width) (inverseNumerator A (D^2) S source N))
    (hdwidth : Denominator.Widths D U V N B) (hDpos : 0 < D) (hUpos : 0 < U) (hVpos : 0 < V)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B) (hrsep : r.Separated a.data)
    (hpp : (Pairing.positive r.channels (inverseNumerator A (D^2) S source N)).bits.length ≤ B)
    (hpn : (Pairing.negative r.channels (inverseNumerator A (D^2) S source N)).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin)
    (hrow : r.Stored (addressValue a.data.width) s.val)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (h141 : Blank s.val 141) (h142 : Blank s.val 142) :
    ∃ cost, ∃ t : Store, cost ≤ calibrationCost N n B ∧ Executes input tape (calibrationCode l) cost s t ∧
      t.val.output = (Pairing.output (Pairing.positive r.channels (inverseNumerator A (D^2) S source N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S source N)) (Denominator.value D U V N)
        (Denominator.value_pos hDpos hUpos hVpos)).encode.reverse ++ s.val.output ∧
      CalibrationMatrix.Ready t.val (dotValues (Pairing.positive r.channels (inverseNumerator A (D^2) S source N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S source N))) ∧
      Word t.val 142 (Denominator.value D U V N) ∧ Blank t.val 106 ∧ Blank t.val 141 ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.randomCursor = s.val.randomCursor ∧
      (∀ i, 150 ≤ i → t.val.tapes i = s.val.tapes i) ∧ Outside a.data s.val t.val := by
  obtain ⟨c1,b,hc1,eb,hbw,hbd,hbp,hbc,hb140,hbf,hbm⟩ := inverse_executes a A (D^2) S source hdecode
    N B hsized hm hn h1 h2 hw hx hprod hscale input tape count outer hcount hcl houter hol origin s hs h140
  have hrowb := hrow.after_inverse hbf hbm hrsep
  have holdb := pairingOld_stored hs.2.1 hbp hbf
  have hwD := RationalAccumulator.word_of_eq (hbf.high _ (by have := l.denominator_ge;omega)) hD
  have hwU := RationalAccumulator.word_of_eq (hbf.high _ (by have := l.numeratorScale_ge;omega)) hU
  have hwV := RationalAccumulator.word_of_eq (hbf.high _ (by have := l.denominatorScale_ge;omega)) hV
  have hwN := RationalAccumulator.word_of_eq (hbf.high _ (by have := l.count_ge;omega)) hN
  obtain ⟨c2,c,hc2,ec,hcw,hcd,hcden,hc141,hcf⟩ := denominator_ready l D U V N B hdwidth
    (a.iterate N).data.finishData (finishResult (a.iterate N).data (a.iterate N).words)
    input tape count b hbw hbd hwD hwU hwV hwN
    (RationalAccumulator.blank_of_eq (hbf.high 141 (by omega)) h141)
    (RationalAccumulator.blank_of_eq (hbf.high 142 (by omega)) h142)
  have hrowc : r.Stored (addressValue (a.iterate N).data.finishData.width) c.val := by
    simpa only [Data.finishData,Snapshot.iterate_width] using hrowb.after_denominator hcf
  have holdc := holdb.after_denominator hcf
  have hsize := a.iterate_sized hsized N
  have hdenbits : (Denominator.value D U V N).bits.length ≤ B := by
    simpa only [Denominator.value_identity] using hdwidth.power N le_rfl
  obtain ⟨c3,t,hc3,et,hto,htr,_,ht106,htf⟩ := pairing_emit r (a.iterate N).data.finishData
    (finishResult (a.iterate N).data (a.iterate N).words) (pairingOld a N) count B
    (Denominator.value D U V N) (Data.finish_sized hsize) hn hrp hrn hsized.2.2.1 hsized.2.2.2.1
    (hsize.2.2.2.2.1 10) (hsize.2.2.2.2.1 11) hcount hcl
    (Denominator.value_pos hDpos hUpos hVpos) hdenbits
    (by simpa only [hbc] using hpp) (by simpa only [hbc] using hpn)
    input tape c hcw hcd hrowc holdc hcden
  refine ⟨c1+(c2+c3),t,?_,eb.seq (ec.seq et),?_,?_,
    RationalAccumulator.word_of_eq (htf.2.2.2 142 (by omega)) hcden,ht106,
    RationalAccumulator.blank_of_eq (htf.2.2.2 141 (by omega)) hc141,
    htf.2.1.trans (hcf.2.1.trans hbf.1),htf.2.2.1.trans (hcf.2.2.2.1.trans hbf.2.1),
    fun i hi => (htf.2.2.2 i (by omega)).trans
      ((hcf.2.2.2.2.2.1 i (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans (hbf.high i (by omega))),
    hbm.trans (Outside.of_memory (htf.1.trans hcf.2.2.1))⟩
  · dsimp [calibrationCost];omega
  · simpa only [hbc,hcf.2.2.2.2.1,hbf.2.2.1] using hto
  · simpa only [hbc] using htr

theorem calibration_compiled_run {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S U V : ℕ)
    (source : Channels n) (r : PairingRow n) (l : Denominator.Layout)
    (hdecode : a.Decodes A (D^2) S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (h1 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (horner A (D^2) S source k).2))
    (h2 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (matvec A (horner A (D^2) S source k).2)))
    (hw : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A (D^2) S source (k+1)).1)
    (hx : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A (D^2) S source (k+1)).2)
    (hprod : FitsWidth (addressValue a.data.width) (matvec A (horner A (D^2) S source N).2))
    (hscale : FitsWidth (addressValue a.data.width) (inverseNumerator A (D^2) S source N))
    (hdwidth : Denominator.Widths D U V N B) (hDpos : 0 < D) (hUpos : 0 < U) (hVpos : 0 < V)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B) (hrsep : r.Separated a.data)
    (hpp : (Pairing.positive r.channels (inverseNumerator A (D^2) S source N)).bits.length ≤ B)
    (hpn : (Pairing.negative r.channels (inverseNumerator A (D^2) S source N)).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin)
    (hrow : r.Stored (addressValue a.data.width) s.val)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (h141 : Blank s.val 141) (h142 : Blank s.val 142) :
    ∃ t : Store,
      (runPriced ((calibrationCode l).compile.next input tape) (calibrationCost N n B+1) s.val).finished =
        some (t.place (calibrationCode l).size) ∧
      (runPriced ((calibrationCode l).compile.next input tape) (calibrationCost N n B+1) s.val).instructions ≤
        6000000*(N+1)*(n+1)^2*(B+2)^2 ∧
      t.val.output = (Pairing.output (Pairing.positive r.channels (inverseNumerator A (D^2) S source N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S source N)) (Denominator.value D U V N)
        (Denominator.value_pos hDpos hUpos hVpos)).encode.reverse ++ s.val.output ∧
      CalibrationMatrix.Ready t.val (dotValues (Pairing.positive r.channels (inverseNumerator A (D^2) S source N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S source N))) ∧
      Word t.val 142 (Denominator.value D U V N) ∧ Blank t.val 106 ∧ Blank t.val 141 ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.randomCursor = s.val.randomCursor ∧
      (∀ i, 150 ≤ i → t.val.tapes i = s.val.tapes i) ∧ Outside a.data s.val t.val := by
  obtain ⟨cost,t,hc,he,ht⟩ := calibration_executes a A D S U V source r l hdecode N B hsized hm hn
    h1 h2 hw hx hprod hscale hdwidth hDpos hUpos hVpos hrp hrn hrsep hpp hpn input tape count outer
    hcount hcl houter hol origin s hs h140 hrow hD hU hV hN h141 h142
  have hr := he.compiled_run (calibrationCost N n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hc.trans (calibrationCost_le N n B),ht⟩

end Maxwell.Cost.CalibrationMatrix.Horner
