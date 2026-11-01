import Maxwell.Continuum.ParameterSourceSelected
import Maxwell.Cost.Structured.Prefix

/-! The already-checked source program has one common parser prefix. This
explicit finite continuation permits the uniform encoder to select its case
before normalization and geometry construction begin. -/
namespace Maxwell.Continuum.Parameters.SourceSelected
open Maxwell.Cost Maxwell.Cost.Structured

def continuation (κ η e : ℕ) : Code :=
  let normalized : Code:=.seq
    (.seq (SourceMetadata.code κ η) (.seq SourceReplay.code NormalizeSource.matrixPassCode))
    NormalizeSource.Rhs.code
  let prepared : Code:=.seq normalized (.seq SourceCircuit.Initialize.code NormalizedRecordParser.rewindCode)
  let allocated : Code:=.seq prepared SourceCircuit.AllocationPass.code
  let started : Code:=.seq allocated SourceCircuit.ArithmeticPrelude.code
  let compiled : Code:=.seq started SourceCircuit.ArithmeticPass.code
  let square : Code:=.seq compiled SparseEmission.code
  let counted : Code:=.seq square SourceGraph.Prepare.suffixCode
  let initialized : Code:=.seq counted PositiveGraph.Initialize.code
  let retained : Code:=.seq initialized SourceGraph.Retain.code
  let graph : Code:=.seq retained PositiveGraph.Pass.code
  let incidence : Code:=.seq graph GraphIncidence.passCode
  let geometry : Code:=.seq incidence (SourceExecution.code κ η e)
  .seq geometry SourceOuter.code

theorem parser_prefix (κ η e : ℕ) :
    Code.Prefix MagnitudeMax.Branch.code (code κ η e) (continuation κ η e) := by
  repeat first
    | exact Code.Prefix.here _
    | apply Code.Prefix.seq

#print axioms parser_prefix
end Maxwell.Continuum.Parameters.SourceSelected
