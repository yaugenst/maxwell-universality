import Maxwell.Cost.SourceCircuit.ArithmeticPrelude.Setup

namespace Maxwell.Cost.SourceCircuit.ArithmeticPrelude
open Structured

def leafWords (S : Source.SparseSystem) (p : ℕ) : List (List Bool) :=
  ((AllocateSource.bank S p).outputs.map Fin.val).map
    (fixedWidth (InitializeMetadata.width S.nnz p))

def data (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) : ArithmeticPass.Data :=
  let allocated := AllocateSource.finalData S p roots memory
  ⟨allocated.next,allocated.gates,leafWords S p,[],[],[]⟩

theorem leafWords_flatten (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) (h : AllocateSource.Result S p roots memory s) :
    (leafWords S p).flatten = (AllocateSource.finalData S p roots memory).leaves := h.leaves.symm

theorem leafWords_length (S : Source.SparseSystem) (p : ℕ) :
    (leafWords S p).length = AllocationPass.occurrences (AllocateSource.records S p) := by
  simp only [leafWords,List.length_map,AllocateSource.bank,Logical.CopyBank.Allocation.output_count,
    AllocationPass.requests_length]

set_option maxRecDepth 8192 in
theorem ready (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (s t : Store) (hs : Preparation.Result S p roots s.val)
    (ht : AllocateSource.Result S p roots s.val.memory t) (hf : AllocationPass.Persistent s t) :
    ArithmeticPass.Ready (AllocateSource.clock S p) p (data S p roots s.val.memory) t := by
  obtain ⟨po,oo,hr⟩ := ht.ready
  have fresh (i : ℕ) (hi : 10 ≤ i) (hsw : i ∉ Preparation.work)
      (htw : i ∉ AllocationPass.work) : t.val.tapes i = BitTape.blank :=
    (hf.tapes i (Or.inr hi) htw).trans (hs.fresh i hi hsw)
  refine ⟨hr.allocation.scratch,hr.allocation.blank7,hr.allocation.blank94,hr.allocation.blank96,
    ⟨0,fresh 99 (by decide) (by decide) (by decide)⟩,
    fresh 103 (by decide) (by decide) (by decide),hr.allocation.next,hr.allocation.gates,
    ?_,?_,?_,hr.allocation.clock,⟨po,hr.power⟩,hr.blank10,hr.blank15,hr.blank16,
    ⟨oo,hr.blank83⟩⟩
  · simpa [data,BitTape.atEnd,BitTape.ofList,BitTape.blank] using
      fresh 104 (by decide) (by decide) (by decide)
  · simpa [data,BitTape.atEnd,BitTape.ofList,BitTape.blank] using
      fresh 105 (by decide) (by decide) (by decide)
  · refine ⟨0,?_⟩
    simpa [data,BitTape.shifted,BitTape.blank] using
      fresh 106 (by decide) (by decide) (by decide)

theorem shape (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) (h : AllocateSource.Result S p roots memory s) :
    ArithmeticPass.Shape (InitializeMetadata.width S.nnz p) (data S p roots memory) := by
  refine ⟨h.valid.length,?_,by simp [data],rfl,by simp [data]⟩
  intro word hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact fixedWidth_length _ _

private theorem gateCost_le (S : Source.SparseSystem) (p : ℕ) :
    ((AllocateSource.records S p).map ArithmeticPass.termGateCost).sum ≤ S.nnz*(2*p+2) := by
  have hgen (rs : List (AllocationPass.Record S.n))
      (h : ∀ r ∈ rs, r.bits.length = p) :
      (rs.map ArithmeticPass.termGateCost).sum ≤ rs.length*(2*p+2) := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      have hb : r.negative.toNat ≤ 1 := by cases r.negative <;> decide
      have hc := List.count_le_length (a := true) (l := r.bits)
      rw [h r (by simp)] at hc
      have ht := ih (fun t ht => h t (by simp [ht]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,ArithmeticPass.termGateCost,
        h r (by simp)]
      nlinarith
  simpa only [AllocateSource.records_length] using hgen (AllocateSource.records S p)
    (AllocateSource.records_precision S p)

theorem valid (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) (hm : 1 ≤ S.nnz)
    (hp : 1 ≤ p) (roots : RootInitData S.n) (memory : ℕ → Bool) (s : Store)
    (h : AllocateSource.Result S p roots memory s)
    (flags : List Bool) (hflags : flags.length = S.nnz) :
    ArithmeticPass.Valid (InitializeMetadata.width S.nnz p)
      (AllocateSource.records S p) flags (data S p roots memory) := by
  refine ⟨shape S p roots memory s h,by simpa using hflags,leafWords_length S p,?_⟩
  have hnext := h.represented.next
  have hbank := (AllocateSource.bank S p).allocation
  change (AllocateSource.bank S p).bank.size = S.n+2*(AllocationPass.requests (AllocateSource.records S p)).length at hbank
  rw [AllocationPass.requests_length] at hbank
  have hc := AllocateSource.records_occurrences S p
  have hg := gateCost_le S p
  have hf := List.count_le_length (a := true) (l := flags)
  rw [hflags] at hf
  have hmSize := Nat.lt_size_self S.nnz
  have hpSize := Nat.lt_size_self p
  have hproduct : S.nnz*p < 2^S.nnz.size*2^p.size := by
    have hpos : 0 < 2^S.nnz.size := by positivity
    nlinarith
  have hpositive : 0 < 2^S.nnz.size*2^p.size := by positivity
  change addressValue (AllocateSource.finalData S p roots memory).next+
    (((AllocateSource.records S p).map ArithmeticPass.termGateCost).sum+
      (AllocateSource.records S p).length+flags.count true+0+1) < _
  rw [hnext,hbank,AllocateSource.records_length]
  have hbudget : S.n+2*AllocationPass.occurrences (AllocateSource.records S p)+
      (((AllocateSource.records S p).map ArithmeticPass.termGateCost).sum+S.nnz+flags.count true+0+1)
      ≤ 10*(S.nnz*p) := by nlinarith
  simp only [InitializeMetadata.width,InitializeMetadata.exponent,pow_add]
  norm_num
  nlinarith only [hproduct,hbudget,hpositive]

end Maxwell.Cost.SourceCircuit.ArithmeticPrelude
