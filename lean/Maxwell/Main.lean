import Maxwell.Source
import Maxwell.Target
import Maxwell.TargetAccess
import Maxwell.Codec
import Maxwell.Codec.Output
import Maxwell.BaseCases
import Maxwell.Cost.BitRAM

-- The retained-edge sum/product index makes the full matrix-ring instance
-- exceed Lean's default synthesis-size limit; no proof checking is disabled.
set_option synthInstance.maxSize 1024

/-! The exact quantitative realization contract.

This module currently defines the proposition that the full construction must
prove. Defining it is not a proof of its inhabitance. In particular no encoder,
spectral platform, or successful decoder is postulated here as an axiom.
The finite-code clauses use the explicit charged-address Boolean RAM model.
The existence theorem for these programs remains a proof obligation.
-/

namespace Maxwell
namespace Realization

open scoped Matrix

/-- Fixed constants, independent of the sparse input and every random draw. -/
structure Constants where
  overhead : ℕ
  logPower : ℕ
  coefficientBits : ℕ
  conditionPower : ℕ
  tolerancePower : ℕ
  stencilSize : ℕ
  overhead_pos : 0 < overhead
  coefficientBits_pos : 0 < coefficientBits
  conditionPower_pos : 0 < conditionPower
  tolerancePower_pos : 0 < tolerancePower

/-- `max 2 m` makes the counted finite base cases explicit. It equals `m`
throughout the probabilistic large-input statement. -/
def effectiveSize (S : Source.SparseSystem) : ℕ := max 2 S.nnz

noncomputable def sizeBudget (C : Constants) (S : Source.SparseSystem) : ℝ :=
  C.overhead * (effectiveSize S : ℝ) ^ (3 / 2 : ℝ) *
    (Real.log (2 + (S.nnz : ℝ))) ^ C.logPower

def bitBudget (C : Constants) (S : Source.SparseSystem) : ℕ :=
  C.coefficientBits * unsignedBitLength (2 + S.nnz)

/-- The emitted material and source belong to the exact dyadic subring. -/
def IsDyadic (q : ℚ) : Prop := ∃ precision, ∃ d : Dyadic precision, d.value = q

/-- Complete every-draw representation bounds, including cells, empty space,
all source entries, every stored readout coefficient, and every input word.
The machine theorem must separately charge writing and reading these bytes. -/
def Resources (C : Constants) (S : Source.SparseSystem) (I : Target.Instance S.n) : Prop :=
  0 < I.box.nx ∧ 0 < I.box.ny ∧ 0 < I.box.nz ∧ 0 < I.dimension ∧
  (I.dimension : ℝ) ≤ sizeBudget C S ∧
  (I.cellCount : ℝ) ≤ sizeBudget C S ∧
  (I.decoder.sampleCount : ℝ) ≤ sizeBudget C S ∧
  I.decoder.format.width ≤ bitBudget C S ∧
  (∀ c, IsDyadic (I.material.value c)) ∧
  (∀ e, IsDyadic (I.source e)) ∧
  (∀ c, Source.ShortRational (bitBudget C S) (I.material.value c)) ∧
  (∀ e, Source.ShortRational (bitBudget C S) (I.source e)) ∧
  Source.ShortRational (bitBudget C S) I.tolerance ∧
  (∀ i, Source.ShortRational (bitBudget C S) (I.decoder.offset i)) ∧
  (∀ i, (I.decoder.support i).card ≤ C.stencilSize) ∧
  (∀ i j, j ∈ I.decoder.support i →
    Source.ShortRational (bitBudget C S) (I.decoder.weight i j)) ∧
  (∀ w i, Source.ShortRational (bitBudget C S) (I.decoder.decode w i)) ∧
  (max 1 S.nnz : ℝ) ^ (-(C.tolerancePower : ℝ)) ≤ (I.tolerance : ℝ)

/-- One good event contains full-matrix conditioning and all-output recovery.
`Fits` and actual bounded-message existence prevent a vacuous readout claim.
The decoder guarantee covers every message at the prescribed accuracy,
including all admissible rounding choices, and every allowed requested eta. -/
def GoodDraw (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (I : Target.Instance S.n) : Prop :=
  IsUnit I.realMatrix ∧
  condition₂ I.realMatrix ≤ (max 1 S.nnz : ℝ) ^ (C.conditionPower : ℝ) ∧
  ∀ y : EuclideanSpace ℂ I.box.Edge, I.Admissible y →
    I.decoder.Fits (fun e => (y e).re) ∧
    (∃ w : I.decoder.Messages, I.decoder.Accurate w (fun e => (y e).re)) ∧
    ∀ w : I.decoder.Messages, I.decoder.Accurate w (fun e => (y e).re) →
      ∀ eta : ℝ, Source.RequestedAccuracy p S eta →
        Source.ResidualTarget S eta (I.decoder.decode w)

/-- A finite uniform random draw consists of exactly this many bits. -/
abbrev Draw (randomBits : ℕ) := Fin (2 ^ randomBits)

def randomTape {randomBits : ℕ} (draw : Draw randomBits) (i : ℕ) : Bool :=
  if i < randomBits then draw.val.testBit i else false

noncomputable def goodDraws (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) {randomBits : ℕ}
    (emitted : Draw randomBits → Target.Instance S.n) : Finset (Draw randomBits) :=
  @Finset.filter _ (fun draw => GoodDraw p C S (emitted draw))
    (Classical.decPred _) Finset.univ

/-- Exact cardinal probability on the actual finite uniform draw space. -/
noncomputable def successProbability (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) {randomBits : ℕ}
    (emitted : Draw randomBits → Target.Instance S.n) : ℝ :=
  ((goodDraws p C S emitted).card : ℝ) / (2 : ℝ) ^ randomBits

/-- A successful encoder execution writes exactly the complete concrete
target representation. It cannot read an unencoded requested eta, return an
opaque target oracle, or consume randomness beyond the finite draw space. -/
def Encodes (encoder : Cost.BitRAM) (S : Source.SparseSystem) {randomBits : ℕ}
    (draw : Draw randomBits) (fuel : ℕ) (I : Target.Instance S.n) : Prop :=
  ∃ stop : Cost.BitRAMState,
    (encoder.run (Codec.source S) (randomTape draw) fuel).finished = some stop ∧
    stop.output.reverse = Codec.target I ∧ stop.randomCursor = randomBits

/-- Deterministic decoding is an actual finite program on the emitted target
bytes and fixed-width field messages. This applies to every bit pattern,
including messages from a bad draw or an inaccurate solver output. -/
def Decodes (decoder : Cost.BitRAM) (outputBits : ℕ) {n : ℕ}
    (I : Target.Instance n) (fuel : ℕ) : Prop :=
  ∀ messages : I.decoder.Messages, ∃ stop : Cost.BitRAMState,
    (decoder.run (Codec.target I ++ Codec.messages I.decoder messages)
      (fun _ => false) fuel).finished = some stop ∧
    Codec.RepresentsOutput outputBits (I.decoder.decode messages) stop.output.reverse ∧
    stop.randomCursor = 0

/-- The full uniform quantified realization statement, with concrete finite
machine code and one success event. This is the proposition to be proved by
the physical/logical construction; declaring this `Prop` does not prove it. -/
def QuantitativeRealization (p : Source.Parameters) : Prop :=
  ∃ C : Constants, ∃ encoder decoder : Cost.BitRAM,
    ∀ S : Source.SparseSystem, Source.Promises p S →
      ∃ randomBits : ℕ,
      ∃ emitted : Draw randomBits → Target.Instance S.n,
      ∃ encoderFuel decoderFuel : Draw randomBits → ℕ,
        (∀ draw, Encodes encoder S draw (encoderFuel draw) (emitted draw)) ∧
        (∀ draw, Decodes decoder (bitBudget C S) (emitted draw) (decoderFuel draw)) ∧
        (∀ draw, Resources C S (emitted draw)) ∧
        (∀ draw, ((encoderFuel draw + decoderFuel draw : ℕ) : ℝ) ≤ sizeBudget C S) ∧
        (2 ≤ S.nnz →
          1 - 3 / (64 * (S.nnz : ℝ)) ≤ successProbability p C S emitted) ∧
        (S.nnz ≤ 1 → ∀ draw, GoodDraw p C S (emitted draw))

/-- The encoder's actual output and random draw are both charged by the
finite program execution, for every draw rather than only the good event. -/
theorem encodes_output_random_le (encoder : Cost.BitRAM) (S : Source.SparseSystem)
    {randomBits : ℕ} (draw : Draw randomBits) (fuel : ℕ) (I : Target.Instance S.n)
    (h : Encodes encoder S draw fuel I) :
    (Codec.target I).length + randomBits ≤ fuel := by
  obtain ⟨stop, hrun, hout, hrandom⟩ := h
  have hb := encoder.run_output_random_bound (Codec.source S) (randomTape draw) fuel stop hrun
  rw [hrandom] at hb
  have hlen : stop.output.length = (Codec.target I).length := by
    simpa only [List.length_reverse] using congrArg List.length hout
  simpa only [hlen] using hb

/-- The fixed finite base construction actually satisfies the complete
all-output event. Its recovery uses the literal requested base tolerance;
the decoder's coefficients contain only zero and need no scalar solve. -/
theorem base_goodDraw (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) :
    GoodDraw p C S (BaseCases.zeroInstance S) := by
  refine ⟨BaseCases.zero_instance_isUnit S, ?_, ?_⟩
  · rw [BaseCases.zero_instance_condition]
    have hmax : max (1 : ℝ) (S.nnz : ℝ) = 1 :=
      max_eq_left (by exact_mod_cast hm)
    simp [hmax]
  · intro y _
    refine ⟨BaseCases.zero_decoder_fits S _,
      ⟨BaseCases.zero_messages S, BaseCases.zero_decoder_accurate S _ _⟩, ?_⟩
    intro w _ eta heta
    exact BaseCases.zero_recovery_requested p S hunit hm eta heta w

end Realization
end Maxwell
