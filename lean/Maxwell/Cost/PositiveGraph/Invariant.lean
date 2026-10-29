import Maxwell.Cost.PositiveGraph.Invariant.DiagonalSource

namespace Maxwell.Cost.PositiveGraph.Invariant
open Maxwell.Logical

/-- The actual final four-bit payload decodes to the exact rational diagonal.
Only the final coefficient bound is used; intermediate sums may wrap modulo16. -/
theorem source_diagonal_value (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length)
    (hinit : initial.diagonal=Initialize.constantWords (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) 4 8)
    (i : Fin (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length)) :
    ((codeAt (sourceTables W S p initial).diagonal i : ℤ)-8 : ℚ)/2 =
      Composition.PositiveRational.diagonal S p (Fin.cast (by omega) i) := by
  rw [source_diagonal_exact W S p initial hinit]
  have hg : (sourceDiagonalWords S p).get i=FixedWidth.bits 4
      (diagonalCode ((Composition.PositiveScatter.numerator S p).get (Fin.cast (by omega) i))).bits := by
    simp [sourceDiagonalWords,Vector.get,Fin.cast]
  unfold codeAt
  rw [hg]
  have hv := IncidenceEncoding.word_value 4
    (diagonalCode ((Composition.PositiveScatter.numerator S p).get (Fin.cast (by omega) i)))
    (diagonalCode_lt _)
  change addressValue (FixedWidth.bits 4 _)=_ at hv
  rw [hv]
  exact PositiveGraph.source_diagonal_code S p (Fin.cast (by omega) i)

/-- Both arrays produced by the finite sparse pass are the actual paper graph. -/
theorem source_tables_exact (W : ℕ) (S : Source.SparseSystem) (p : ℕ)
    (hd : (sourceCircuit S p).size<2^W)
    (initial : Tables (sourceCircuit S p).size (sourceSquareEntries S p).length)
    (hinit : initial.diagonal=Initialize.constantWords (2*(sourceCircuit S p).size+(sourceSquareEntries S p).length) 4 8) :
    (sourceTables W S p initial).endpoints=sourceEndpointWords W S p ∧
      (sourceTables W S p initial).diagonal=sourceDiagonalWords S p :=
  ⟨source_endpoints_exact W S p hd initial,source_diagonal_exact W S p initial hinit⟩

end Maxwell.Cost.PositiveGraph.Invariant
