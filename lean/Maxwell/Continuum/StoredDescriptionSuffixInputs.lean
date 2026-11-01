import Maxwell.Continuum.StoredSourcePhysical
import Maxwell.Continuum.StoredReadoutPhysical
import Maxwell.Continuum.StoredDecoderPhysical

/-! The suffix boundary records actual words and arrays left by well
serialization. It contains no execution premise or preinitialized row loop. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word)

def suffixOldPorts : List ℕ:=SourcePayload.parseWords++[85,972,4808]++
  DecoderRow.outputList++RationalCanonical.workspace
def suffixSelectorPorts : Finset ℕ:=DecoderRow.headerPorts.toFinset∪DecoderRow.selectorPorts

structure SuffixStored (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (v nv : ℕ→ℕ)
    (saved : SourceEmission.Geometry
      ((sourceCircuit S (RealizationParameters.precision p S hm)).size+(sourceCircuit S (RealizationParameters.precision p S hm)).size+
        (sourceSquareEntries S (RealizationParameters.precision p S hm)).length)
      ((sourceSquareEntries S (RealizationParameters.precision p S hm)).length+(sourceSquareEntries S (RealizationParameters.precision p S hm)).length))
    (table : PartArray.Table (siteCount saved)) (R H : ℕ) (clock : List Bool)
    (gv : ℕ→ℕ) (rv : ℕ→Parts) (s : Store) : Prop where
  geometry : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
    clock (Geometry.values v) gv s
  payload : WellPayload.State table (wellStoredPrecision p S hm) R (siteCount saved)
    (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) rv s
  raw : Ready WellStrength.bank (Function.update (WellStrengthPhysical.values p S hm data) 0 (rv 0)) s
  clean : DyadicFloor.Clean s.val
  power : Word s.val 144 (2^wellStoredPrecision p S hm)
  sourceNumerator : Word s.val 506 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word s.val 507 (NormalizeRatio.sourceScalePair S).2
  sourcePrecision : Word s.val 4427 (RealizationParameters.sourcePrecision p S)
  archive : BankArray.Word s.val 508 (LogRats.records (List.ofFn S.source))
  first : Word s.val 503 (sourceCircuit S (RealizationParameters.precision p S hm)).size
  selectors : NatAssign.Bank suffixSelectorPorts nv s.val
  old : WordCleanup.Bounded suffixOldPorts H s.val

def suffixCode : Code:=.seq SourcePayload.completeCode (.seq GeometryOutput.Readout.code decoderCode)
def suffixWork : Finset ℕ:=SourcePayload.completeWork∪GeometryOutput.Readout.work∪decoderWork
def suffixBits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) : List Bool:=
  sourceStream p S hm++readoutPlacementStream p S hm++Cost.FiniteDecoder.description (decoder p S hm)
def suffixSourceWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (R H : ℕ) : ℕ:=
  sourceInitialWidth p S hm data R (H+(2^wellStoredPrecision p S hm).bits.length)
def suffixRawWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (R H : ℕ) : ℕ:=
  sourceBankWidth p S (suffixSourceWidth p S hm data R H)
def suffixCost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (v nv : ℕ→ℕ) (R H J : ℕ) : ℕ:=
  sourceCost p S hm v (suffixSourceWidth p S hm data R H)
    (H+(2^wellStoredPrecision p S hm).bits.length) H H+
  (GeometryOutput.Readout.costBound (geometryBudget v) S.n+
    decoderCost (wellStoredPrecision p S hm) (geometryBudget v)
      (decoderBankWidth p S hm v nv (suffixRawWidth p S hm data R H) R)
      (H+(2^sourcePrecision p S).bits.length)
      (sourceCircuit S (RealizationParameters.precision p S hm)).size S.n J S.n.bits.length)

end Maxwell.Continuum.WellStrengthInitialization
