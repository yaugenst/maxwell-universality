import Maxwell.Cost.SourceCircuit.ArithmeticPrelude.State
import Maxwell.Cost.SourceCircuit.AllocateSource.Bounds

namespace Maxwell.Cost.SourceCircuit.ArithmeticPrelude
open Structured

def flags (S : Source.SparseSystem) : List Bool :=
  SourceGrouping.markers [] false (Codec.sourceRecord S).entries

@[simp] theorem flags_length (S : Source.SparseSystem) : (flags S).length = S.nnz := by
  rw [flags,SourceGrouping.markers_length,Logical.CachedNormalization.sourceRecord_eq]
  simp

def sourceCode (k c : ℕ) : Code := .seq (AllocateSource.code k c) code

noncomputable def sourcePrice (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  let precision := Realization.binaryCoefficientPrecision S.nnz k c
  AllocateSource.price p S k c+
    price S.nnz (Preparation.archive S precision) (leafWords S precision).flatten (flags S)

structure Result (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) : Prop where
  ready : ArithmeticPass.Ready (AllocateSource.clock S p) p (data S p roots memory) s
  shape : ArithmeticPass.Shape (InitializeMetadata.width S.nnz p) (data S p roots memory)
  room : ∀ fs : List Bool, fs.length = S.nnz →
    ArithmeticPass.Valid (InitializeMetadata.width S.nnz p) (AllocateSource.records S p) fs
      (data S p roots memory)
  counter : RationalAccumulator.Word s.val 100 S.nnz
  archive : s.val.tapes 85 = NormalizedRecordParser.cursor (Preparation.archive S p) 0
  leaves : s.val.tapes 98 = Increment.cursor [] (data S p roots memory).leaves.flatten 0
  markers : s.val.tapes 24 = Increment.cursor [] (flags S) 0

set_option maxRecDepth 8192 in
theorem executes (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz)
    (hm : 1 ≤ S.nnz) (hp : 1 ≤ p) (input : List Bool) (tape : ℕ → Bool)
    (roots : RootInitData S.n) (pre allocated : Store)
    (hs : Preparation.Result S p roots pre.val)
    (ha : AllocateSource.Result S p roots pre.val.memory allocated)
    (hf : AllocationPass.Persistent pre allocated) :
    ∃ t, Executes input tape code
        (price S.nnz (Preparation.archive S p) (leafWords S p).flatten (flags S)) allocated t ∧
      Result S p roots pre.val.memory t ∧ BinaryPrecision.Frame work allocated.val t.val := by
  obtain ⟨co,counter,hcounter,hlen⟩ := ha.counter
  obtain ⟨po,oo,haReady⟩ := ha.ready
  have h79 : RationalAccumulator.Word allocated.val 79 S.nnz :=
    RationalAccumulator.word_of_eq (hf.tapes 79 (by decide) (by decide)) hs.count
  have h85 : allocated.val.tapes 85 = BitTape.atEnd (Preparation.archive S p) := by
    simpa [NormalizedRecordParser.cursor,BitTape.atEnd] using ha.cursor
  have h98 : allocated.val.tapes 98 = BitTape.atEnd (leafWords S p).flatten := by
    rw [leafWords_flatten S p roots pre.val.memory allocated ha]
    exact haReady.allocation.leaves
  have h24 : allocated.val.tapes 24 = BitTape.atEnd (flags S) :=
    (hf.tapes 24 (by decide) (by decide)).trans hs.markers
  obtain ⟨t,et,t100,t85,t98,t24,ft⟩ := setup input tape S.nnz (Preparation.archive S p)
    (leafWords S p).flatten (flags S) counter co allocated h79 hcounter hlen h85 h98 h24
  refine ⟨t,et,⟨ready_transport (ready S p roots pre allocated hs ha hf) ft,
    shape S p roots pre.val.memory allocated ha,
    fun fs hfs => valid S p hn hm hp roots pre.val.memory allocated ha fs hfs,t100,?_,?_,?_⟩,ft⟩
  · simpa [NormalizedRecordParser.cursor,BitTape.ofList] using t85
  · simpa [data,Increment.cursor,BitTape.shifted,BitTape.ofList] using t98
  · simpa [Increment.cursor,BitTape.shifted,BitTape.ofList] using t24

set_option maxRecDepth 8192 in
/-- Canonical source bytes produce the full state needed by the uniform
Horner/row-sum pass, including physically rewound leaves and row markers. -/
theorem source_executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost pre allocated t roots,
      Executes (Codec.source S) tape (sourceCode k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ sourcePrice p S k c ∧
      Preparation.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val ∧
      AllocateSource.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory allocated ∧
      AllocationPass.Persistent pre allocated ∧ BinaryPrecision.Frame work allocated.val t.val ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory t := by
  obtain ⟨ac,pre,allocated,roots,ea,hac,hpre,ha,hf⟩ := AllocateSource.executes p S hp hm hb k c tape
  obtain ⟨t,et,ht,ft⟩ := executes S (Realization.binaryCoefficientPrecision S.nnz k c)
    (Source.dimension_le_nnz S hp.1) (by omega) (Realization.binaryCoefficientPrecision_pos _ _ _)
    (Codec.source S) tape roots pre allocated hpre ha hf
  exact ⟨_,pre,allocated,t,roots,ea.seq et,Nat.add_le_add_right hac _,hpre,ha,hf,ft,ht⟩

end Maxwell.Cost.SourceCircuit.ArithmeticPrelude
