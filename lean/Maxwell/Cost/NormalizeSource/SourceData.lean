import Maxwell.Cost.NormalizeSource.Loop
import Maxwell.Cost.NormalizeRatio.SourceData
import Maxwell.Cost.MagnitudeMax.SourceSemantics

namespace Maxwell.Cost.NormalizeSource
open Logical Logical.Normalization

noncomputable def sourceWidth (p : Source.Parameters) (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  MagnitudeMax.inputWidth p S + S.nnz.bits.length + precision + 1

/-- Every bound required by the finite coefficient loop follows from the
actual sparse-source promise and the chosen precision. -/
theorem source_width (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (precision : ℕ) (hs : 1 ≤ precision) :
    ∀ entry ∈ (Codec.sourceRecord S).entries,
      Width (NormalizeRatio.matrixScalePair S).1 (NormalizeRatio.matrixScalePair S).2 precision
        (sourceWidth p S precision) entry := by
  have hwidth := MagnitudeMax.promised_entry_width p S hp
  have hvalues : ∀ q ∈ matrixValues S,
      q.num.natAbs.bits.length ≤ MagnitudeMax.inputWidth p S ∧
        q.den.bits.length ≤ MagnitudeMax.inputWidth p S := by
    intro q hq
    rw [← MagnitudeMax.source_values S] at hq
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
    exact (hwidth entry he).2.2
  have hscale := NormalizeRatio.matrixScalePair_bits S (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth_pos p S) (fun q hq => (hvalues q hq).1) (fun q hq => (hvalues q hq).2)
  intro entry he
  obtain ⟨hr, hc, hn, hd⟩ := hwidth entry he
  refine ⟨by dsimp [sourceWidth]; omega, by dsimp [sourceWidth]; omega, ?_, ?_⟩
  · intro i hi hj
    interval_cases i
    all_goals simp only [NormalizeCoefficient.values, Function.update_apply, Codec.RationalPair.canonical]
    all_goals norm_num
    all_goals first
      | (dsimp [sourceWidth]; omega)
      | (rw [PowerOfTwo.power_bits]; simp; dsimp [sourceWidth]; omega)
  · rw [Logical.CachedNormalization.sourceRecord_eq, Logical.CachedNormalization.stored_eq,
      List.map_map] at he
    obtain ⟨ij, _, rfl⟩ := List.mem_map.mp he
    simp only [Function.comp_apply]
    unfold roundedNumerator
    rw [NormalizeRatio.matrixScalePair_value]
    exact nearest_numerator_lt precision hs _ (normalizedMatrix_half_bound S hm ij.1 ij.2)

/-- Exact wire format of a typed coefficient term, including its original
row/column and all leading coefficient zero bits. -/
def termWire {n : ℕ} (term : Fin n × DyadicTerm n) : List Bool :=
  SourceCircuit.normalizedRecord term.1.val term.2.input.val term.2.negative term.2.bits

/-- The machine's archived stream is exactly the logical compiler's input
stream, without reordering or dropping coefficients rounded to zero. -/
theorem source_records (S : Source.SparseSystem) (precision : ℕ) :
    records (NormalizeRatio.matrixScalePair S).1 (NormalizeRatio.matrixScalePair S).2 precision
      (Codec.sourceRecord S).entries =
        (Logical.CachedNormalization.sourceTerms S precision).flatMap termWire := by
  rw [records, Logical.CachedNormalization.sourceRecord_eq,
    Logical.CachedNormalization.stored_eq, List.flatMap_map, List.flatMap_map,
    Logical.CachedNormalization.sourceTerms_eq, List.flatMap_map]
  apply congrArg (fun f => (Codec.sourceEntries S).flatMap f)
  funext ij
  simp [record, roundedNumerator, NormalizeRatio.matrixScalePair_value,
    termWire, dyadicTerm, normalizedMatrix]
  rfl

end Maxwell.Cost.NormalizeSource
