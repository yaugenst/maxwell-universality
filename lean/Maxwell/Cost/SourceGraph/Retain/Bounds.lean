import Maxwell.Cost.SourceGraph.Retain.Core
import Maxwell.Cost.NormalizeSource.SourceData

namespace Maxwell.Cost.SourceGraph.Retain
open Structured

/-- All copied scale words have widths derived from the original rational
input promises; no word-width advice is supplied to retention. -/
theorem initial_width (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (precision : ℕ) :
    ∀ i ∈ ids, (initial S precision i).bits.length ≤ NormalizeSource.sourceWidth p S precision := by
  have hwidth := MagnitudeMax.promised_entry_width p S hp
  have hvalues : ∀ q ∈ Logical.Normalization.matrixValues S,
      q.num.natAbs.bits.length ≤ MagnitudeMax.inputWidth p S ∧
        q.den.bits.length ≤ MagnitudeMax.inputWidth p S := by
    intro q hq
    rw [← MagnitudeMax.source_values S] at hq
    obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hq
    exact (hwidth entry he).2.2
  have hm := NormalizeRatio.matrixScalePair_bits S (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth_pos p S) (fun q hq => (hvalues q hq).1) (fun q hq => (hvalues q hq).2)
  have rhs := MagnitudeMax.promised_rhs_width p S hp
  have hb := MagnitudeMax.maximum_width (List.ofFn S.source) (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth p S) (MagnitudeMax.inputWidth_pos p S)
    (fun q hq => (rhs q hq).1) (fun q hq => (rhs q hq).2)
  change (NormalizeRatio.sourceScalePair S).1.bits.length ≤ _ ∧
    (NormalizeRatio.sourceScalePair S).2.bits.length ≤ _ at hb
  have hn : S.n.bits.length ≤ S.nnz.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size (Source.dimension_le_nnz S hp.1)
  have hprec : precision.bits.length ≤ precision := by
    simpa only [WordLength.countBits_eq] using WordLength.countBits_length precision
  have hpow : (2^precision).bits.length = precision+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
  intro i _
  dsimp [initial,NormalizeSource.sourceWidth]
  split_ifs <;> first | omega | simp_all

theorem numericPrice_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (precision : ℕ) :
    numericPrice S precision ≤ 3000*8^statements.length*(NormalizeSource.sourceWidth p S precision+2)^2 :=
  NatAssign.price_bound ids statements valid (initial S precision)
    (NormalizeSource.sourceWidth p S precision) (initial_width p S hp precision)
    (by simp [statements,NatAssign.Instruction.literalWidth])

theorem rhs_length (S : Source.SparseSystem) :
    (LogRats.records (List.ofFn S.source)).length ≤ (Codec.source S).length := by
  simp only [LogRats.records,Codec.source,Codec.vector,Codec.list,List.length_append]
  omega

end Maxwell.Cost.SourceGraph.Retain
