import Maxwell.Cost.SourceCircuit.AllocateSource.Readiness

namespace Maxwell.Cost.SourceCircuit.AllocateSource
open Structured

def code (k c : ℕ) : Code := .seq (Preparation.code k c) AllocationPass.code

def passPrice (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  AllocationPass.costBound (records S p) (wordWidth S p) [] (clock S p) S.nnz.bits

noncomputable def price (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  Preparation.price p S k c+passPrice S (Realization.binaryCoefficientPrecision S.nnz k c)

def finalData (S : Source.SparseSystem) (p : ℕ) (data : RootInitData S.n)
    (memory : ℕ → Bool) : AllocationData S.n :=
  AllocationPass.allocate 0 (InitializeMetadata.width S.nnz p) (records S p) (initial S p data memory)

def bank (S : Source.SparseSystem) (p : ℕ) :=
  (Logical.CopyBank.initial S.n).allocate (AllocationPass.requests (records S p))

structure Result (S : Source.SparseSystem) (p : ℕ) (data : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) : Prop where
  ready : ∃ powerOrigin outputOrigin : ℤ,
    AllocationPass.Ready (wordWidth S p)
      (AllocationPass.finalIndex (clock S p).length (records S p) data.index)
      [] (clock S p) p powerOrigin outputOrigin (finalData S p data memory) s
  valid : AllocationPass.Valid 0 (InitializeMetadata.width S.nnz p) [] (finalData S p data memory)
  represented : (finalData S p data memory).Matches (InitializeMetadata.width S.nnz p) (bank S p).bank
  trace : traceBytes (InitializeMetadata.width S.nnz p)
      ((Logical.CopyBank.initial S.n).trace (AllocationPass.requests (records S p))) =
    some (copyArchive (InitializeMetadata.width S.nnz p)
      (Logical.CopyBank.initial S.n) (AllocationPass.requests (records S p)))
  gates : (finalData S p data memory).gates =
    copyArchive (InitializeMetadata.width S.nnz p)
      (Logical.CopyBank.initial S.n) (AllocationPass.requests (records S p))
  leaves : (finalData S p data memory).leaves =
    ((bank S p).outputs.map Fin.val).flatMap (fixedWidth (InitializeMetadata.width S.nnz p))
  cursor : s.val.tapes 85 = NormalizedRecordParser.cursor
    (Preparation.archive S p) (Preparation.archive S p).length
  counter : ∃ counterOrigin : ℤ, ∃ finalCounter : List Bool,
    s.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧
      finalCounter.length = S.nnz.bits.length

set_option maxRecDepth 8192 in
theorem step (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) (hp : 1 ≤ p)
    (input : List Bool) (tape : ℕ → Bool) (data : RootInitData S.n)
    (s : Store) (h : Preparation.Result S p data s.val) :
    ∃ cost t, Executes input tape AllocationPass.code cost s t ∧ cost ≤ passPrice S p ∧
      Result S p data s.val.memory t ∧ AllocationPass.Persistent s t := by
  obtain ⟨po,oo,co,hr,hcounter⟩ := prepared_ready S p data s h
  have hwidth : addressValue (wordWidth S p) = InitializeMetadata.width S.nnz p := addressValue_bits _
  have hclock : (clock S p).length = addressValue (wordWidth S p) := (clock_length S p).trans hwidth.symm
  have hvalid : AllocationPass.Valid (addressValue []) (addressValue (wordWidth S p))
      (records S p) (initial S p data s.val.memory) := by
    simpa only [hwidth,addressValue] using initial_valid S p hn hp data s.val h
  obtain ⟨cost,t,finalCounter,hcost,he,ht,hv,h85,h100,hlen,hf⟩ := AllocationPass.executes input tape
    (records S p) [] [] (wordWidth S p) data.index [] (clock S p) S.nnz.bits p po oo co
    (initial S p data s.val.memory) s
    (RationalAccumulator.bits_nonempty (InitializeMetadata.width_pos _ _)) hclock
    (by rw [clock_length]; exact InitializeMetadata.width_pos _ _)
    (by intro r _; rw [clock_length]; exact width_fit S p hn r.column)
    (records_precision S p) (by rw [addressValue_bits,records_length]) hcounter hr hvalid
    (prepared_cursor S p data s.val h)
  obtain ⟨hmatch,htrace,hgates,hleaves⟩ := AllocationPass.binding 0
    (InitializeMetadata.width S.nnz p) (records S p) (Logical.CopyBank.initial S.n)
    (initial S p data s.val.memory) (initial_matches S p hn data s.val h)
    (records_room S p hn hp)
  refine ⟨cost,t,he,hcost,?_,hf⟩
  refine ⟨⟨po,oo,?_⟩,?_,hmatch,htrace,?_,?_,?_,⟨co,finalCounter,h100,hlen⟩⟩
  · simpa only [finalData,hwidth,addressValue] using ht
  · simpa only [finalData,hwidth,addressValue] using hv
  · simpa only [finalData,initial,List.nil_append] using hgates
  · simpa only [finalData,bank,initial,List.nil_append] using hleaves
  · simpa only [List.nil_append,List.append_nil,List.length_nil,Nat.cast_zero,zero_add,records_wire] using h85

set_option maxRecDepth 8192 in
/-- The fixed finite program starts with the canonical sparse input and
emits the logical copy-bank gates and leaves. Its intermediate root table
and normalized coefficient stream are produced by actual instructions. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost s t data, Executes (Codec.source S) tape (code k c) cost
        (Store.ofState BitRAMState.initial) t ∧ cost ≤ price p S k c ∧
      Preparation.Result S (Realization.binaryCoefficientPrecision S.nnz k c) data s.val ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) data s.val.memory t ∧
      AllocationPass.Persistent s t := by
  obtain ⟨pc,s,data,ep,hpc,hs⟩ := Preparation.executes p S hp hm hb k c tape
  obtain ⟨ac,t,ea,hac,ht,hf⟩ := step S (Realization.binaryCoefficientPrecision S.nnz k c)
    (Source.dimension_le_nnz S hp.1) (Realization.binaryCoefficientPrecision_pos _ _ _)
    (Codec.source S) tape data s hs
  exact ⟨pc+ac,s,t,data,ep.seq ea,Nat.add_le_add hpc hac,hs,ht,hf⟩

end Maxwell.Cost.SourceCircuit.AllocateSource
