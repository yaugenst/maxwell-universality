import Maxwell.Cost.CalibrationMatrix.SourceInit.Width
import Maxwell.Cost.CalibrationMatrix.Horner.Calibration

namespace Maxwell.Cost.CalibrationMatrix.SourceInit
open Structured
open RationalAccumulator (Blank Word)
open scoped BigOperators
set_option maxHeartbeats 2000000

def calibrationCode (l : Horner.Denominator.Layout) : Code :=
  .seq readyCode (Horner.calibrationCode l)

def calibrationCost (m N n B : ℕ) : ℕ := readyCost m n B+Horner.calibrationCost N n B

theorem calibrationCost_le (m N n B : ℕ) :
    calibrationCost m N n B ≤ 8000000*(m+N+1)*(n+1)^2*(B+2)^2 := by
  have hc := Horner.calibrationCost_le N n B
  have hs : 84*B+85 ≤ 1000000*(B+2)^2 := by nlinarith [Nat.zero_le (B^2)]
  dsimp [calibrationCost,readyCost,costBound]
  nlinarith only [hc,hs,Nat.zero_le
    ((8000000*m*n^2+16000000*m*n+7000000*m+
      2000000*N*n^2+4000000*N*n+2000000*N+2000000*n^2+3000000*n)*(B+2)^2)]

theorem outside_horner {m n : ℕ} {d : Data m n} {h : Horner.Data n}
    (hwidth : d.width = h.width)
    (hbases : ∀ i : Fin 4, d.outputBases i = h.bases ⟨i.val,by omega⟩)
    {s t : BitRAMState} (hout : Outside d s t) : Horner.Outside h s t := by
  intro address ha
  apply hout address
  intro i
  rw [hbases,hwidth]
  exact ha ⟨i.val,by omega⟩

/-- The sparse-record initializer, descriptor setup, finite inverse,
denominator construction, and scalar emitter execute as one instruction
stream. One common width covers source scatter and every inverse iterate. -/
theorem calibration_executes {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (hwidth : d.width = h.width)
    (hbases : ∀ i : Fin 4, d.outputBases i = h.bases ⟨i.val,by omega⟩)
    (initial : Fin 12 → Vector (List Bool) n) (A : ChannelMatrix n) (D S U V : ℕ)
    (hA : h.DecodesMatrix A) (hK : h.K = (D^2)^3) (hS : h.S = S)
    (r : Horner.PairingRow n) (l : Horner.Denominator.Layout)
    (N B : ℕ) (hd : d.Sized B) (hh : h.Sized B)
    (hm : m < 2^B) (hn : n < 2^B) (hnn : n*n < 2^B)
    (matrixBound : ℕ) (hAb : A.Bounded matrixBound)
    (hslots : Horner.uniformWidth n matrixBound (totalBound d) (D^2) S N ≤ addressValue d.width)
    (hdwidth : Horner.Denominator.Widths D U V N B)
    (hDpos : 0 < D) (hUpos : 0 < U) (hVpos : 0 < V)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B)
    (hrsep : r.Separated h)
    (hpp : (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N)).bits.length ≤ B)
    (hpn : (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N)).bits.length ≤ B)
    (old : Fin 4 → List Bool) (hold : ∀ i, (old i).length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (outer : List Bool)
    (houter : addressValue outer = N) (hol : outer.length ≤ B) (origin : ℤ) (s : Store)
    (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (fun i => initial ⟨i.val,by omega⟩) s.val)
    (hhdata : Horner.Stored h initial s.val)
    (h102 : BankArray.Word s.val 102 []) (h103 : BankArray.Word s.val 103 [])
    (h104 : BankArray.Word s.val 104 []) (h37 : Blank s.val 37)
    (h106 : Blank s.val 106) (h108 : Blank s.val 108) (h109 : Blank s.val 109)
    (hports : ∀ i : Fin 4, BankArray.Word s.val (112+i.val) (old i))
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin)
    (hrow : r.Stored (addressValue h.width) s.val)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (h141 : Blank s.val 141) (h142 : Blank s.val 142) :
    ∃ cost, ∃ t : Store, cost ≤ calibrationCost m N n B ∧
      Executes input tape (calibrationCode l) cost s t ∧
      t.val.output = (Pairing.output
        (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Horner.Denominator.value D U V N) (Horner.Denominator.value_pos hDpos hUpos hVpos)).encode.reverse ++
          s.val.output ∧
      Ready t.val (dotValues
        (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N))) ∧
      Word t.val 142 (Horner.Denominator.value D U V N) ∧ Blank t.val 106 ∧ Blank t.val 141 ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.randomCursor = s.val.randomCursor ∧
      (∀ i, 150 ≤ i → t.val.tapes i = s.val.tapes i) ∧ Horner.Outside h s.val t.val := by
  obtain ⟨hp,hq⟩ := totals_fit d matrixBound (D^2) S N _ hslots
  obtain ⟨sc,a,hsc,ea,ar,af,aout,akeep⟩ := ready d h hwidth hbases initial B hd hh hm hn hp hq old hold
    input tape s hready hdata hhdata h102 h103 h104 h37 h106 h108 h109 hports
  have hout := outside_horner hwidth hbases aout
  have ra : r.Stored (addressValue h.width) a.val :=
    ⟨BankArray.word_of_eq (akeep 154 (by omega)) hrow.positiveBase,
      BankArray.word_of_eq (akeep 155 (by omega)) hrow.negativeBase,
      Horner.represents_of_horner_outside hrow.positive hout hrsep.1,
      Horner.represents_of_horner_outside hrow.negative hout hrsep.2⟩
  have bounds (k : ℕ) (hk : k ≤ N) := Horner.uniform_width hAb (D^2) S (values d.records m)
    (values_bounded d m) N (addressValue h.width) (hwidth ▸ hslots) k hk
  obtain ⟨cc,t,hcc,et,toutput,tr,t142,t106,t141,ti,tq,tk,tout⟩ :=
    Horner.calibration_executes (snapshot d h initial) A D S U V (values d.records m) r l
      (snapshot_decodes d h initial A (D^2) S hA hK hS hp hq) N B hh hnn hn
      (fun k hk => (bounds k (by omega)).2.2.1)
      (fun k hk => (bounds k (by omega)).2.2.2.1)
      (fun k hk => (bounds (k+1) (by omega)).1)
      (fun k hk => (bounds (k+1) (by omega)).2.1)
      (bounds N le_rfl).2.2.1 (bounds N le_rfl).2.2.2.2
      hdwidth hDpos hUpos hVpos hrp hrn hrsep hpp hpn input tape d.dimension outer
      d.dimension_value hd.2.2.1 houter hol origin a ar ((akeep 140 (by omega)).trans h140) ra
      (RationalAccumulator.word_of_eq (akeep _ (by have := l.denominator_ge;omega)) hD)
      (RationalAccumulator.word_of_eq (akeep _ (by have := l.numeratorScale_ge;omega)) hU)
      (RationalAccumulator.word_of_eq (akeep _ (by have := l.denominatorScale_ge;omega)) hV)
      (RationalAccumulator.word_of_eq (akeep _ (by have := l.count_ge;omega)) hN)
      (RationalAccumulator.blank_of_eq (akeep 141 (by omega)) h141)
      (RationalAccumulator.blank_of_eq (akeep 142 (by omega)) h142)
  exact ⟨sc+cc,t,by dsimp [calibrationCost];omega,ea.seq et,by rw [toutput,af.2.2.1],
    tr,t142,t106,t141,ti.trans af.1,tq.trans af.2.1,
    fun i hi => (tk i hi).trans (akeep i (by omega)),hout.trans tout⟩

theorem calibration_run {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (hwidth : d.width = h.width)
    (hbases : ∀ i : Fin 4, d.outputBases i = h.bases ⟨i.val,by omega⟩)
    (initial : Fin 12 → Vector (List Bool) n) (A : ChannelMatrix n) (D S U V : ℕ)
    (hA : h.DecodesMatrix A) (hK : h.K = (D^2)^3) (hS : h.S = S)
    (r : Horner.PairingRow n) (l : Horner.Denominator.Layout)
    (N B : ℕ) (hd : d.Sized B) (hh : h.Sized B)
    (hm : m < 2^B) (hn : n < 2^B) (hnn : n*n < 2^B)
    (matrixBound : ℕ) (hAb : A.Bounded matrixBound)
    (hslots : Horner.uniformWidth n matrixBound (totalBound d) (D^2) S N ≤ addressValue d.width)
    (hdwidth : Horner.Denominator.Widths D U V N B)
    (hDpos : 0 < D) (hUpos : 0 < U) (hVpos : 0 < V)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B)
    (hrsep : r.Separated h)
    (hpp : (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N)).bits.length ≤ B)
    (hpn : (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N)).bits.length ≤ B)
    (old : Fin 4 → List Bool) (hold : ∀ i, (old i).length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (outer : List Bool)
    (houter : addressValue outer = N) (hol : outer.length ≤ B) (origin : ℤ) (s : Store)
    (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (fun i => initial ⟨i.val,by omega⟩) s.val)
    (hhdata : Horner.Stored h initial s.val)
    (h102 : BankArray.Word s.val 102 []) (h103 : BankArray.Word s.val 103 [])
    (h104 : BankArray.Word s.val 104 []) (h37 : Blank s.val 37)
    (h106 : Blank s.val 106) (h108 : Blank s.val 108) (h109 : Blank s.val 109)
    (hports : ∀ i : Fin 4, BankArray.Word s.val (112+i.val) (old i))
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin)
    (hrow : r.Stored (addressValue h.width) s.val)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (h141 : Blank s.val 141) (h142 : Blank s.val 142) :
    ∃ t : Store,
      (runPriced ((calibrationCode l).compile.next input tape) (calibrationCost m N n B+1) s.val).finished =
        some (t.place (calibrationCode l).size) ∧
      (runPriced ((calibrationCode l).compile.next input tape) (calibrationCost m N n B+1) s.val).instructions ≤
        calibrationCost m N n B ∧
      t.val.output = (Pairing.output
        (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Horner.Denominator.value D U V N) (Horner.Denominator.value_pos hDpos hUpos hVpos)).encode.reverse ++
          s.val.output ∧
      Ready t.val (dotValues
        (Pairing.positive r.channels (inverseNumerator A (D^2) S (values d.records m) N))
        (Pairing.negative r.channels (inverseNumerator A (D^2) S (values d.records m) N))) ∧
      Word t.val 142 (Horner.Denominator.value D U V N) ∧ Blank t.val 106 ∧ Blank t.val 141 ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.randomCursor = s.val.randomCursor ∧
      (∀ i, 150 ≤ i → t.val.tapes i = s.val.tapes i) ∧ Horner.Outside h s.val t.val := by
  obtain ⟨cost,t,hcost,he,post⟩ := calibration_executes d h hwidth hbases initial A D S U V hA hK hS
    r l N B hd hh hm hn hnn matrixBound hAb hslots hdwidth hDpos hUpos hVpos hrp hrn hrsep hpp hpn
    old hold input tape outer houter hol origin s hready hdata hhdata h102 h103 h104 h37 h106 h108 h109
    hports h140 hrow hD hU hV hN h141 h142
  have hr := he.compiled_run (calibrationCost m N n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hcost,post⟩

end Maxwell.Cost.CalibrationMatrix.SourceInit
