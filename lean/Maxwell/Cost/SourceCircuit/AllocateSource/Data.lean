import Maxwell.Cost.SourceCircuit.PreparationBounds
import Maxwell.Cost.SourceCircuit.AllocationPass
import Maxwell.Cost.SourceCircuit.AllocationPassTrace

namespace Maxwell.Cost.SourceCircuit.AllocateSource

def records (S : Source.SparseSystem) (p : ℕ) : List (AllocationPass.Record S.n) :=
  (Logical.CachedNormalization.sourceTerms S p).map fun term =>
    ⟨term.1.val, term.2.input, term.2.negative, term.2.bits⟩

@[simp] theorem records_length (S : Source.SparseSystem) (p : ℕ) :
    (records S p).length = S.nnz := by simp [records]

theorem records_wire (S : Source.SparseSystem) (p : ℕ) :
    AllocationPass.wire (records S p) = Preparation.archive S p := by
  simp only [records, AllocationPass.wire, List.flatMap_map, Preparation.archive]
  rfl

theorem records_precision (S : Source.SparseSystem) (p : ℕ)
    (r : AllocationPass.Record S.n) (hr : r ∈ records S p) : r.bits.length = p := by
  rw [records,Logical.CachedNormalization.sourceTerms_eq] at hr
  obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hr
  simp only [List.mem_map] at *
  rename_i term
  obtain ⟨ij,_,rfl⟩ := term
  simp [Logical.Normalization.dyadicTerm,Logical.Horner.encode_length]

theorem records_row (S : Source.SparseSystem) (p : ℕ)
    (r : AllocationPass.Record S.n) (hr : r ∈ records S p) : r.row < S.n := by
  obtain ⟨term,_,rfl⟩ := List.mem_map.mp hr
  exact term.1.isLt

private theorem occurrences_le {n : ℕ} (rs : List (AllocationPass.Record n)) (p : ℕ)
    (h : ∀ r ∈ rs, r.bits.length = p) : AllocationPass.occurrences rs ≤ rs.length*p := by
  induction rs with
  | nil => simp [AllocationPass.occurrences]
  | cons r rest ih =>
    have hr := List.count_le_length (a := true) (l := r.bits)
    rw [h r (by simp)] at hr
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [AllocationPass.occurrences,List.map_cons,List.sum_cons,List.length_cons]
    change r.bits.count true+AllocationPass.occurrences rest ≤ (rest.length+1)*p
    nlinarith

theorem records_occurrences (S : Source.SparseSystem) (p : ℕ) :
    AllocationPass.occurrences (records S p) ≤ S.nnz*p := by
  simpa only [records_length] using occurrences_le (records S p) p (records_precision S p)

theorem records_room (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) (hp : 1 ≤ p) :
    S.n+2*AllocationPass.occurrences (records S p) < 2^InitializeMetadata.width S.nnz p := by
  have h := InitializeMetadata.width_room S.n S.nnz p hn hp
  have hc := records_occurrences S p
  nlinarith

theorem width_fit (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz)
    (i : Fin S.n) : i.val.bits.length ≤ InitializeMetadata.width S.nnz p := by
  have h := Nat.size_le_size (show i.val ≤ S.nnz by omega)
  simp only [InitializeMetadata.width,InitializeMetadata.exponent,Nat.size_eq_bits_len] at *
  omega

theorem dimension_fit (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) :
    S.n.bits.length ≤ InitializeMetadata.width S.nnz p := by
  have h := Nat.size_le_size hn
  simp only [InitializeMetadata.width,InitializeMetadata.exponent,Nat.size_eq_bits_len] at *
  omega

def initial (S : Source.SparseSystem) (p : ℕ) (data : RootInitData S.n)
    (memory : ℕ → Bool) : AllocationData S.n where
  roots := data.roots
  next := FixedWidth.bits (InitializeMetadata.width S.nnz p) S.n.bits
  gates := []
  leaves := []
  memory := memory

theorem initial_valid (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) (hp : 1 ≤ p)
    (data : RootInitData S.n) (s : BitRAMState) (h : Preparation.Result S p data s) :
    AllocationPass.Valid 0 (InitializeMetadata.width S.nnz p) (records S p) (initial S p data s.memory) := by
  refine ⟨h.compiler.array, FixedWidth.bits_length _ _, ?_⟩
  change addressValue (FixedWidth.bits (InitializeMetadata.width S.nnz p) S.n.bits)+_ < _
  rw [FixedWidth.bits_value _ _ (dimension_fit S p hn),addressValue_bits]
  exact records_room S p hn hp

theorem initial_matches (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz)
    (data : RootInitData S.n) (s : BitRAMState) (h : Preparation.Result S p data s) :
    (initial S p data s.memory).Matches (InitializeMetadata.width S.nnz p) (Logical.CopyBank.initial S.n) := by
  refine ⟨h.compiler.roots, h.compiler.array.length, ?_, FixedWidth.bits_length _ _⟩
  change addressValue (FixedWidth.bits (InitializeMetadata.width S.nnz p) S.n.bits) = S.n
  rw [FixedWidth.bits_value _ _ (dimension_fit S p hn),addressValue_bits]

end Maxwell.Cost.SourceCircuit.AllocateSource
