import Maxwell.Continuum.ContinuumGridReports
import Maxwell.Continuum.FiniteDecoderCost
import Maxwell.Continuum.ContinuumRawReportWords

/-! The continuum decoder uses explicit physical grid addresses and one
stored rational weight per original variable. Its actual finite program is
the standalone serialized-stencil decoder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision messageRangeBits

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def readoutSite (i : Fin S.n) : SourceDecoration.Vertex S (precision p S hm) :=
  Sum.inl (SourceRouting.inputCoordinate S (precision p S hm) i)

def decoder : Target.WeightedDecoder (Fin (gridCount p S hm)) S.n where
  sampleCount := gridCount p S hm
  coordinate := id
  format := gridReportFormat p S hm
  support := fun i => {gridAddress p S hm (readoutSite p S hm i)}
  weight := fun i _ => normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i)
  offset := fun _ => 0

theorem decoder_support (i : Fin S.n) : ((decoder p S hm).support i).card=1 := by
  simp [decoder]

theorem decoder_value (w : (decoder p S hm).Messages) :
    (decoder p S hm).decode w=decodeRawReports p S hm (gridRawReports p S hm w) := by
  change (Fin (gridCount p S hm) → (gridReportFormat p S hm).Word) at w
  funext i
  simp only [Target.WeightedDecoder.decode,decoder,Finset.sum_singleton,zero_add,
    decodeRawReports,sparseMomentDecode,PositiveRecovery.decode,weightedRawReports,
    gridRawReports,readoutSite,normalizationScale]
  rw [gridReportWord_value p S hm
    (w (gridAddress p S hm (Sum.inl (SourceRouting.inputCoordinate S (precision p S hm) i))))]
  ring

def gridFieldReports
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) :
    Fin (gridCount p S hm) → ℝ := fun q =>
  (inner ℂ (gridTemplate p S hm q)
    (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re

theorem decoder_accurate (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (w : (decoder p S hm).Messages)
    (hw : (decoder p S hm).Accurate w (gridFieldReports p S hm u)) :
    ∀i,|((rawReportDyadic p S hm (gridRawReports p S hm w i)).value : ℝ)-
      (inner ℂ (selectedTemplates p S hm i)
        (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re|≤
      (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) := by
  intro i
  have hi := hw (gridAddress p S hm i)
  change |((gridReportFormat p S hm).value (w (gridAddress p S hm i)) : ℝ)-
    gridFieldReports p S hm u (gridAddress p S hm i)|≤1/(2 : ℝ)^momentPrecision p S at hi
  rw [gridFieldReports,gridTemplate_address] at hi
  simp only [gridRawReports]
  rw [gridReportWord_value p S hm (w (gridAddress p S hm i))]
  apply hi.trans
  have h := moment_precision_budget p S hm hm2 huS
  simpa only [one_div,inv_pow] using h

theorem decoder_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (w : (decoder p S hm).Messages)
    (hw : (decoder p S hm).Accurate w (gridFieldReports p S hm u))
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    Source.ResidualTarget S eta ((decoder p S hm).decode w) := by
  rw [decoder_value]
  exact computed_raw_report_recovery p S hm hm2 hp hb j hgood u hu (gridRawReports p S hm w)
    (decoder_accurate p S hm hm2 hp.1 u w hw) eta heta

theorem decoder_output_words (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (w : (decoder p S hm).Messages) (i : Fin S.n) :
    Maxwell.rationalBitLength ((decoder p S hm).decode w i)≤
      (2*decodedWordCoefficient p+1)*logSize S := by
  rw [decoder_value]
  exact decodeRawReports_word_bits p S hm hm2 hp hb (gridRawReports p S hm w) i

/-- The concrete continuum stencil is executed by a single fixed program,
from its initial state, for every finite report pattern. -/
theorem decoder_runs (w : (decoder p S hm).Messages) (randomTape : ℕ → Bool) :
    ∃ stop : Cost.BitRAMState,
      (Cost.runPriced (FiniteDecoder.program.next
        (FiniteDecoder.description (decoder p S hm)++Codec.messages (decoder p S hm) w) randomTape)
        (FiniteDecoder.costCap (decoder p S hm)+1) Cost.BitRAMState.initial).finished=some stop ∧
      (Cost.runPriced (FiniteDecoder.program.next
        (FiniteDecoder.description (decoder p S hm)++Codec.messages (decoder p S hm) w) randomTape)
        (FiniteDecoder.costCap (decoder p S hm)+1) Cost.BitRAMState.initial).instructions≤
          FiniteDecoder.costCap (decoder p S hm) ∧
      Codec.RepresentsOutput (Cost.DecoderParser.decoderWidth (decoder p S hm)+2)
        ((decoder p S hm).decode w) stop.output.reverse ∧ stop.randomCursor=0 :=
  FiniteDecoder.run (decoder p S hm) w randomTape

#print axioms decoder_value
#print axioms decoder_recovery
#print axioms decoder_output_words
#print axioms decoder_runs

end Maxwell.Continuum.RealizationParameters
