import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Cost.SourceCircuit.FinalMetadata

namespace Maxwell.Cost.SourceGraph.Retain
open Structured
open RationalAccumulator (Word Blank)

def ids : Finset ℕ := {19,79,80,81,82,84,86,87,500,501,502,504,505,506,507,509}
def initial (S : Source.SparseSystem) (p : ℕ) (i : ℕ) : ℕ :=
  if i=19 then S.n else if i=79 then S.nnz else if i=84 then p else if i=82 then 2^p
  else if i=80 then (NormalizeRatio.matrixScalePair S).1
  else if i=81 then (NormalizeRatio.matrixScalePair S).2
  else if i=86 then (NormalizeRatio.sourceScalePair S).1
  else if i=87 then (NormalizeRatio.sourceScalePair S).2 else 0

def statements : List NatAssign.Instruction :=
  [.copy 19 500,.copy 79 501,.copy 84 502,.copy 80 504,.copy 81 505,
    .copy 86 506,.copy 87 507,.copy 82 509]
def numericCode : Code := NatAssign.code statements
def numericPrice (S : Source.SparseSystem) (p : ℕ) := NatAssign.price statements (initial S p)

theorem ids_lower : ∀ i ∈ ids, 4 ≤ i := by decide
theorem valid : ∀ a ∈ statements, a.Valid ids := by
  simp [statements,NatAssign.Instruction.Valid,ids]

/-- These retained words are disjoint from all routing and physical work
banks; the exact rational pairs keep their source-computed representation. -/
structure Numeric (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState) : Prop where
  dimension : Word s 500 S.n
  count : Word s 501 S.nnz
  precisionWord : Word s 502 p
  matrixNumerator : Word s 504 (NormalizeRatio.matrixScalePair S).1
  matrixDenominator : Word s 505 (NormalizeRatio.matrixScalePair S).2
  sourceNumerator : Word s 506 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word s 507 (NormalizeRatio.sourceScalePair S).2
  power : Word s 509 (2^p)

theorem numeric_of_bank (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (h : NatAssign.Bank ids (NatAssign.values statements (initial S p)) s) : Numeric S p s := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 500 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 501 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 502 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 504 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 505 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 506 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 507 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using h 509 (by decide)

end Maxwell.Cost.SourceGraph.Retain
