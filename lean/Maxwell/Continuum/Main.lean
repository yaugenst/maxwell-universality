import Maxwell.Source.Size
import Maxwell.Continuum.ContinuumDecoderPolynomial
import Maxwell.Continuum.ContinuumFiniteReports
import Maxwell.Continuum.ContinuumFairDetuning

/-! The exact uniform continuum realization contract.

The physical fields, finite reports, and output bytes below are the existing
concrete constructions. One leading Boolean distinguishes the fixed vacuum
format from the computed format. In either branch the decoder receives the
entire emitted description followed by the finite message stream.

This file states the proposition still to be proved. It does not assume an
encoder, an execution trace, a resource bound, or the final theorem. The
component theorems do not establish `QuantitativeRealization` by themselves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Realization

open RealizationParameters SelfAdjointResolvent

/-- Fixed input-independent resource constants. The three resource powers
are the manuscript's volume, description, and joint running-time powers. -/
structure Constants where
  overhead : ℕ
  wordCoefficient : ℕ
  conditionPower : ℕ
  tolerancePower : ℕ
  overhead_pos : 0 < overhead
  wordCoefficient_pos : 0 < wordCoefficient
  conditionPower_pos : 0 < conditionPower
  tolerancePower_pos : 0 < tolerancePower

def budget (C : Constants) (S : Source.SparseSystem) (logPower : ℕ) : ℝ :=
  C.overhead * (S.effectiveSize : ℝ) ^ (3 / 2 : ℝ) *
    (Parameters.inputLog S.nnz : ℝ) ^ logPower

def wordBudget (C : Constants) (S : Source.SparseSystem) : ℕ :=
  C.wordCoefficient * Parameters.inputLog S.nnz

/-- The canonical tape determined by exactly the sampled finite fair bits. -/
def randomTape {r : ℕ} (w : Fin r → Bool) (i : ℕ) : Bool :=
  if h : i < r then w ⟨i, h⟩ else false

/-- A successful run starts from the actual machine initial state and emits
exactly the stated bytes, consuming exactly the stated number of random bits. -/
def Encodes (program : Cost.BitRAM) (S : Source.SparseSystem)
    {r : ℕ} (w : Fin r → Bool) (bytes : List Bool) (fuel : ℕ) : Prop :=
  ∃ stop : Cost.BitRAMState,
    (program.run (Codec.source S) (randomTape w) fuel).finished = some stop ∧
    stop.output.reverse = bytes ∧ stop.randomCursor = r

/-- Decoding includes parsing the complete emitted physical description;
the standalone decoder-header theorem alone does not satisfy this clause. -/
def Decodes {ι : Type} {n : ℕ} (program : Cost.BitRAM)
    (bytes : List Bool) (D : Target.WeightedDecoder ι n)
    (outputWidth fuel : ℕ) : Prop :=
  ∀ messages : D.Messages, ∃ stop : Cost.BitRAMState,
    (program.run (bytes ++ Codec.messages D messages) (fun _ => false) fuel).finished = some stop ∧
    Codec.RepresentsOutput outputWidth (D.decode messages) stop.output.reverse ∧
    stop.randomCursor = 0

/-- The false tag declares the unit vacuum cube, zero source, unit tolerance,
and no volume tests. The serialized zero decoder records the output dimension. -/
def vacuumDecoder (S : Source.SparseSystem) : Target.WeightedDecoder (Fin 0) S.n where
  sampleCount := 0
  coordinate := Fin.elim0
  format := ⟨0, 0⟩
  support _ := ∅
  weight _ := Fin.elim0
  offset := 0

def vacuumBytes (S : Source.SparseSystem) : List Bool :=
  false :: Cost.FiniteDecoder.description (vacuumDecoder S)

def computedBytes (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (j : Fin (drawCount p S hm)) : List Bool :=
  true :: completeDescriptionBits p S hm j

/-- Every-draw bounds for the actual computed box, material, source, volume
tests, serialized description, finite messages, output rationals, and tolerance.
The represented fields are fixed by the definitions, not supplied as oracles. -/
def Resources (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (hm : 0 < S.nnz) (hb : S.source ≠ 0) (j : Fin (drawCount p S hm)) : Prop :=
  (∀ k : Fin 3, 0 < Parameters.sourcePhysicalLengths p S hm k) ∧
  (∀ x : Space, 1 ≤ (computedDielectric p S hm hb j).coefficient x ∧
    (computedDielectric p S hm hb j).coefficient x ≤ 25) ∧
  fieldConjugation (computedSource p S hm : FieldL2) = (computedSource p S hm : FieldL2) ∧
  (∀ q : Fin (gridCount p S hm),
    fieldConjugation (gridTemplate p S hm q) = gridTemplate p S hm q) ∧
  (MeasureTheory.volume (BoxModes.openBox (BoxCutoff.side (box p S hm)))).toReal ≤ budget C S 24 ∧
  ((computedBytes p S hm j).length : ℝ) ≤ budget C S 64 ∧
  (gridCount p S hm : ℝ) ≤ budget C S 24 ∧
  (decoder p S hm).format.width ≤ wordBudget C S ∧
  (∀ w : (decoder p S hm).Messages, ∀ i : Fin S.n,
    rationalBitLength ((decoder p S hm).decode w i) ≤ wordBudget C S) ∧
  0 < residual p S hm ∧
  (S.effectiveSize : ℝ) ^ (-(C.tolerancePower : ℝ)) ≤ (residual p S hm : ℝ) ∧
  rationalBitLength (residual p S hm) ≤ wordBudget C S ∧
  rationalBitLength (energy p S hm) ≤ wordBudget C S ∧
  randomBitCount p S hm ≤ wordBudget C S

/-- One good draw includes the actual PEC inverse, its graph-norm condition,
bounded-message existence, and every-field, every-message residual recovery. -/
def GoodDraw (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (hm : 0 < S.nnz) (hb : S.source ≠ 0) (j : Fin (drawCount p S hm)) : Prop :=
  (∃ R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j)),
    ‖R.map‖ ≤ (inverseBound p S hm : ℝ) ∧
    ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) R‖ ≤ 27 * (inverseBound p S hm : ℝ) ∧
    ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j)‖ *
      ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
        (computedDielectric p S hm hb j) R‖ ≤ (S.effectiveSize : ℝ) ^ C.conditionPower) ∧
  ∀ u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))),
    ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u - computedSource p S hm‖ ≤
      (residual p S hm : ℝ) * ‖computedSource p S hm‖ →
    (decoder p S hm).Fits (gridFieldReports p S hm u) ∧
    (∃ w : (decoder p S hm).Messages, (decoder p S hm).Accurate w (gridFieldReports p S hm u)) ∧
    ∀ w : (decoder p S hm).Messages, (decoder p S hm).Accurate w (gridFieldReports p S hm u) →
      ∀ eta : ℝ, Source.RequestedAccuracy p S eta →
        Source.ResidualTarget S eta ((decoder p S hm).decode w)

/-- The finite base branch uses the actual unit-volume vacuum inverse.
Its resource bound remains positive at `nnz = 0` through the shared
`effectiveSize` convention. Recovery needs no sample of the supplied field. -/
def VacuumBranch (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (encoderProgram decoderProgram : Cost.BitRAM) : Prop :=
  ∃ encoderFuel decoderFuel : ℕ,
    Encodes encoderProgram S (Fin.elim0 : Fin 0 → Bool) (vacuumBytes S) encoderFuel ∧
    Decodes decoderProgram (vacuumBytes S) (vacuumDecoder S) (wordBudget C S) decoderFuel ∧
    ((encoderFuel + decoderFuel : ℕ) : ℝ) ≤ budget C S 4096 ∧
    ((vacuumBytes S).length : ℝ) ≤ budget C S 64 ∧
    (MeasureTheory.volume (BoxModes.openBox VacuumBox.lengths)).toReal ≤ budget C S 24 ∧
    (vacuumDecoder S).format.width ≤ wordBudget C S ∧
    (S.effectiveSize : ℝ) ^ (-(C.tolerancePower : ℝ)) ≤ (VacuumBox.tolerance : ℝ) ∧
    ‖VacuumBox.inverse.map‖ ≤ 1 ∧
    ‖maxwellGraphMap VacuumBox.domain VacuumBox.material‖ *
      ‖maxwellGraphInverse VacuumBox.domain VacuumBox.material VacuumBox.inverse‖ ≤
      (S.effectiveSize : ℝ) ^ C.conditionPower ∧
    ∀ _u : OperatorDomain VacuumBox.domain, ∀ w : (vacuumDecoder S).Messages,
      ∀ eta : ℝ, Source.RequestedAccuracy p S eta →
        Source.ResidualTarget S eta ((vacuumDecoder S).decode w)

/-- The selected fair-bit event is fixed before the solver field and reports.
Every seed is executed and obeys all resource bounds, including bad seeds. -/
def ComputedBranch (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (hm : 0 < S.nnz) (hb : S.source ≠ 0) (encoderProgram decoderProgram : Cost.BitRAM) : Prop :=
  ∃ encoderFuel decoderFuel : (Fin (randomBitCount p S hm) → Bool) → ℕ,
    (∀ w : Fin (randomBitCount p S hm) → Bool,
      let j := randomDraw p S hm w
      Encodes encoderProgram S w (computedBytes p S hm j) (encoderFuel w) ∧
      Decodes decoderProgram (computedBytes p S hm j) (decoder p S hm)
        (wordBudget C S) (decoderFuel w) ∧
      Resources p C S hm hb j ∧
      ((encoderFuel w + decoderFuel w : ℕ) : ℝ) ≤ budget C S 4096) ∧
    (∀ w : Fin (randomBitCount p S hm) → Bool,
      (randomDraw p S hm w).val ∉ computedBadDraws p S hm hb →
        GoodDraw p C S hm hb (randomDraw p S hm w)) ∧
    ((FairBits.law (randomBitCount p S hm)).toOuterMeasure
      {w | (randomDraw p S hm w).val ∈ computedBadDraws p S hm hb}).toReal ≤
        3 / (64 * (S.nnz : ℝ))

/-- Exact final target: one pair of finite programs works for every promised
input. Neither branch accepts precomputed output data or machine traces.
No inhabitant of this proposition is asserted in this module. -/
def QuantitativeRealization (p : Source.Parameters) : Prop :=
  ∃ C : Constants, ∃ encoderProgram decoderProgram : Cost.BitRAM,
    ∀ S : Source.SparseSystem, Source.Promises p S →
      ((S.source = 0 ∨ S.nnz ≤ 1) → VacuumBranch p C S encoderProgram decoderProgram) ∧
      (∀ hm2 : 2 ≤ S.nnz, ∀ hb : S.source ≠ 0,
        ComputedBranch p C S (Nat.lt_of_lt_of_le (by decide : 0 < 2) hm2) hb
          encoderProgram decoderProgram)

end Maxwell.Continuum.Realization
