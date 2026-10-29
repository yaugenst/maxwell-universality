import Maxwell.Cost.CalibrationMatrix.Horner.Calibration
import Maxwell.Cost.CalibrationMatrix.Horner.UniformWidth

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank Word)

/-- A single explicit width linear in the iteration count supplies every
intermediate fit premise of the complete physical calibration program. -/
theorem calibration_uniform {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S U V : ℕ)
    (source : Channels n) (r : PairingRow n) (l : Denominator.Layout)
    (hdecode : a.Decodes A (D^2) S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (matrixBound sourceBound : ℕ) (hA : A.Bounded matrixBound) (hv : source.Bounded sourceBound)
    (hwidth : uniformWidth n matrixBound sourceBound (D^2) S N ≤ addressValue a.data.width)
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
  have bounds (k : ℕ) (hk : k ≤ N) := uniform_width hA (D^2) S source hv N
    (addressValue a.data.width) hwidth k hk
  exact calibration_compiled_run a A D S U V source r l hdecode N B hsized hm hn
    (fun k hk => (bounds k (by omega)).2.2.1)
    (fun k hk => (bounds k (by omega)).2.2.2.1)
    (fun k hk => (bounds (k+1) (by omega)).1)
    (fun k hk => (bounds (k+1) (by omega)).2.1)
    (bounds N le_rfl).2.2.1 (bounds N le_rfl).2.2.2.2
    hdwidth hDpos hUpos hVpos hrp hrn hrsep hpp hpn input tape count outer
    hcount hcl houter hol origin s hs h140 hrow hD hU hV hN h141 h142

end Maxwell.Cost.CalibrationMatrix.Horner
