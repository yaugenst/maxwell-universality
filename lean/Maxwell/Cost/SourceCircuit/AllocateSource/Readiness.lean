import Maxwell.Cost.SourceCircuit.AllocateSource.Data

namespace Maxwell.Cost.SourceCircuit.AllocateSource
open Structured

def wordWidth (S : Source.SparseSystem) (p : ℕ) : List Bool :=
  (InitializeMetadata.width S.nnz p).bits

def clock (S : Source.SparseSystem) (p : ℕ) : List Bool :=
  (2^InitializeMetadata.exponent S.nnz p).bits

theorem clock_length (S : Source.SparseSystem) (p : ℕ) :
    (clock S p).length = InitializeMetadata.width S.nnz p := by
  rw [clock,Nat.size_eq_bits_len,Nat.size_pow]
  rfl

set_option maxRecDepth 8192 in
theorem prepared_ready (S : Source.SparseSystem) (p : ℕ)
    (data : RootInitData S.n) (s : Store) (h : Preparation.Result S p data s.val) :
    ∃ powerOrigin outputOrigin counterOrigin : ℤ,
      AllocationPass.Ready (wordWidth S p) data.index [] (clock S p) p powerOrigin outputOrigin
        (initial S p data s.val.memory) s ∧
      s.val.tapes 100 = BitTape.shifted S.nnz.bits counterOrigin := by
  obtain ⟨powerOrigin,hpower⟩ := h.power
  obtain ⟨outputOrigin,houtput⟩ := h.coefficient
  obtain ⟨counterOrigin,hcounter⟩ := h.compiler.counter
  have blank (i : ℕ) (hi : 10 ≤ i) (hw : i ∉ Preparation.work) :
      RationalAccumulator.Blank s.val i := ⟨0,h.fresh i hi hw⟩
  refine ⟨powerOrigin,outputOrigin,counterOrigin,?_,hcounter⟩
  refine ⟨⟨h.compiler.scratch,h.compiler.seven,
    blank 94 (by decide) (by decide),blank 96 (by decide) (by decide),
    h.compiler.widthWord,h.compiler.indexWord,h.compiler.zeroBase,?_,h.compiler.next,
    ?_,?_,rfl⟩,?_,h.parser.1,h.parser.2.1,h.parser.2.2.1,
    h.compiler.temporary,houtput,hpower⟩
  · simpa only [RationalAccumulator.Word,BankArray.Word,clock] using h.compiler.clock
  · simpa [initial,BitTape.atEnd,BitTape.ofList,BitTape.blank] using h.fresh 97 (by decide) (by decide)
  · simpa [initial,BitTape.atEnd,BitTape.ofList,BitTape.blank] using h.fresh 98 (by decide) (by decide)
  · rw [clock_length]
    exact h.compiler.indexLength

theorem prepared_cursor (S : Source.SparseSystem) (p : ℕ)
    (data : RootInitData S.n) (s : BitRAMState) (h : Preparation.Result S p data s) :
    s.tapes 85 = NormalizedRecordParser.cursor
      ([] ++ (AllocationPass.wire (records S p) ++ [])) 0 := by
  simpa [NormalizedRecordParser.cursor,records_wire,BitTape.ofList] using h.matrixArchive

end Maxwell.Cost.SourceCircuit.AllocateSource
