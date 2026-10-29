import Maxwell.Codec

/-!
# Exact source parsing and faithfulness

The parser reads the actual Boolean serialization into dimension, sparse
coordinate/coefficient triples, and the complete right-hand-side list. Its
roundtrip preserves every bit after the source record. No dense matrix scan,
solution oracle, or proof-field serialization is involved.
-/

namespace Maxwell.Codec

structure SourceRecord where
  dimension : ℕ
  entries : List (ℕ × ℕ × ℚ)
  rhs : List ℚ
  deriving DecidableEq

def sourceEntryValue (S : Source.SparseSystem) (p : {p // p ∈ sourceEntries S}) :
    ℕ × ℕ × ℚ :=
  (p.val.1.val, p.val.2.val,
    S.matrix.coefficient ⟨p.val, (mem_sourceEntries S p.val).mp p.property⟩)

def sourceRecord (S : Source.SparseSystem) : SourceRecord where
  dimension := S.n
  entries := (sourceEntries S).attach.map (sourceEntryValue S)
  rhs := List.ofFn S.source

def readSourceEntry (bs : List Bool) : Option ((ℕ × ℕ × ℚ) × List Bool) := do
  let (i, tail₁) ← readNat bs
  let (j, tail₂) ← readNat tail₁
  let (q, tail₃) ← readRat tail₂
  pure ((i, j, q), tail₃)

def readSource (bs : List Bool) : Option (SourceRecord × List Bool) := do
  let (n, tail₁) ← readNat bs
  let (entries, tail₂) ← readList readSourceEntry tail₁
  let (rhs, tail₃) ← readList readRat tail₂
  pure (⟨n, entries, rhs⟩, tail₃)

theorem readSourceEntry_append (S : Source.SparseSystem)
    (p : {p // p ∈ sourceEntries S}) (tail : List Bool) :
    readSourceEntry (sourceEntry S p ++ tail) = some (sourceEntryValue S p, tail) := by
  simp [readSourceEntry, sourceEntry, sourceEntryValue, List.append_assoc,
    readNat_append, readRat_append]

theorem readMany_map_append {α β : Type*} (encode : α → List Bool)
    (parse : List Bool → Option (β × List Bool)) (decode : α → β)
    (hparse : ∀ x tail, parse (encode x ++ tail) = some (decode x, tail))
    (xs : List α) (tail : List Bool) :
    readMany parse xs.length (xs.flatMap encode ++ tail) = some (xs.map decode, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readMany, List.append_assoc, hparse, ih]

theorem readList_map_append {α β : Type*} (encode : α → List Bool)
    (parse : List Bool → Option (β × List Bool)) (decode : α → β)
    (hparse : ∀ x tail, parse (encode x ++ tail) = some (decode x, tail))
    (xs : List α) (tail : List Bool) :
    readList parse (list encode xs ++ tail) = some (xs.map decode, tail) := by
  simp [readList, list, List.append_assoc, readNat_append,
    readMany_map_append encode parse decode hparse]

/-- The actual complete source wire format has a streaming inverse. -/
theorem readSource_append (S : Source.SparseSystem) (tail : List Bool) :
    readSource (source S ++ tail) = some (sourceRecord S, tail) := by
  simp [readSource, source, vector, List.append_assoc, readNat_append,
    readList_map_append (sourceEntry S) readSourceEntry (sourceEntryValue S)
      (readSourceEntry_append S), readList_append rat readRat readRat_append, sourceRecord]

theorem source_record_eq_of_encoding_eq (S T : Source.SparseSystem)
    (h : source S = source T) : sourceRecord S = sourceRecord T := by
  have hh := congrArg (fun bs => readSource (bs ++ [])) h
  simpa only [readSource_append, Option.some.injEq, Prod.mk.injEq, and_true] using hh

/-- The parsed triples are exactly the original stored support and values. -/
theorem sourceRecord_entry_iff (S : Source.SparseSystem)
    (i j : Fin S.n) (q : ℚ) :
    (i.val, j.val, q) ∈ (sourceRecord S).entries ↔
      ∃ h : (i, j) ∈ S.matrix.support, S.matrix.coefficient ⟨(i, j), h⟩ = q := by
  simp only [sourceRecord, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨⟨⟨i', j'⟩, hp⟩, heq⟩
    simp only [sourceEntryValue, Prod.mk.injEq] at heq
    have hi : i' = i := Fin.ext heq.1
    have hj : j' = j := Fin.ext heq.2.1
    subst i'
    subst j'
    exact ⟨(mem_sourceEntries S (i, j)).mp hp, heq.2.2⟩
  · rintro ⟨hp, hq⟩
    refine ⟨⟨(i, j), (mem_sourceEntries S (i, j)).mpr hp⟩, ?_⟩
    simp [sourceEntryValue, hq]

/-- Every parsed right-hand-side coordinate is its exact input rational. -/
theorem sourceRecord_rhs (S : Source.SparseSystem) (i : Fin S.n) :
    (sourceRecord S).rhs[i.val]'(by simp [sourceRecord]) = S.source i := by
  simp [sourceRecord]

theorem sourceRecord_support_eq {n : ℕ} (M N : SparseRationalMatrix n n)
    (b c : Fin n → ℚ)
    (h : sourceRecord ⟨n, M, b⟩ = sourceRecord ⟨n, N, c⟩) : M.support = N.support := by
  ext p
  constructor
  · intro hp
    have hmem := (sourceRecord_entry_iff ⟨n, M, b⟩ p.1 p.2 (M.coefficient ⟨p, hp⟩)).mpr
      ⟨hp, rfl⟩
    rw [h] at hmem
    exact ((sourceRecord_entry_iff ⟨n, N, c⟩ p.1 p.2 _).mp hmem).choose
  · intro hp
    have hmem := (sourceRecord_entry_iff ⟨n, N, c⟩ p.1 p.2 (N.coefficient ⟨p, hp⟩)).mpr
      ⟨hp, rfl⟩
    rw [← h] at hmem
    exact ((sourceRecord_entry_iff ⟨n, M, b⟩ p.1 p.2 _).mp hmem).choose

/-- Parsed equality determines the complete canonical sparse matrix,
including every stored coefficient and the implicit zeros off support. -/
theorem sourceRecord_matrix_eq {n : ℕ} (M N : SparseRationalMatrix n n)
    (b c : Fin n → ℚ)
    (h : sourceRecord ⟨n, M, b⟩ = sourceRecord ⟨n, N, c⟩) : M = N := by
  have hs := sourceRecord_support_eq M N b c h
  rcases M with ⟨support, coefficient, nonzero⟩
  rcases N with ⟨support', coefficient', nonzero'⟩
  dsimp at hs
  subst support'
  have hc : coefficient = coefficient' := by
    funext p
    have hmem := (sourceRecord_entry_iff
      ⟨n, ⟨support, coefficient, nonzero⟩, b⟩ p.val.1 p.val.2 (coefficient p)).mpr
        ⟨p.property, rfl⟩
    rw [h] at hmem
    obtain ⟨_, hv⟩ := (sourceRecord_entry_iff
      ⟨n, ⟨support, coefficient', nonzero'⟩, c⟩ p.val.1 p.val.2 _).mp hmem
    exact hv.symm
  subst coefficient'
  rfl

/-- No two source instances share the same parsed source record. -/
theorem sourceRecord_injective : Function.Injective sourceRecord := by
  rintro ⟨n, M, b⟩ ⟨n', N, c⟩ h
  have hn := congrArg SourceRecord.dimension h
  change n = n' at hn
  subst n'
  have hm := sourceRecord_matrix_eq M N b c h
  have hb := congrArg SourceRecord.rhs h
  change List.ofFn b = List.ofFn c at hb
  have hbc := List.ofFn_injective hb
  subst N
  subst c
  rfl

/-- The actual Boolean source serialization is injective on complete
`SparseSystem` values; proof fields are irrelevant, as intended. -/
theorem source_injective : Function.Injective source := by
  intro S T h
  exact sourceRecord_injective (source_record_eq_of_encoding_eq S T h)

end Maxwell.Codec
