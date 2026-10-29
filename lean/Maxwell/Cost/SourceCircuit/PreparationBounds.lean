import Maxwell.Cost.SourceCircuit.Preparation

namespace Maxwell.Cost.SourceCircuit.Preparation

private theorem flatMap_length_bound {α β : Type} (f : α → List β) (xs : List α) (B : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

theorem archive_length (S : Source.SparseSystem) (precision : ℕ)
    (hn : S.n ≤ S.nnz) :
    (archive S precision).length ≤ S.nnz*(4*S.nnz.size+precision+3) := by
  rw [archive,Logical.CachedNormalization.sourceTerms_eq,List.flatMap_map]
  have h := flatMap_length_bound
    (fun ij : Fin S.n × Fin S.n => NormalizeSource.termWire
      (ij.1,Logical.Normalization.dyadicTerm precision
        (Logical.Normalization.normalizedMatrix S ij.1 ij.2) ij.2))
    (Codec.sourceEntries S) (4*S.nnz.size+precision+3) (by
      intro ij _
      have hr := Nat.size_le_size (show ij.1.val ≤ S.nnz by omega)
      have hc := Nat.size_le_size (show ij.2.val ≤ S.nnz by omega)
      simp only [NormalizeSource.termWire,normalizedRecord,Codec.nat,List.length_append,
        List.length_replicate,List.length_cons,List.length_nil,
        Logical.Normalization.dyadicTerm,Logical.Horner.encode_length,Nat.size_eq_bits_len]
      omega)
  simpa only [Codec.sourceEntries_length,Function.comp_apply] using h

/-- The complete executed prefix, including actual root-array writes and
the archive rewind, has a near-linear bit-operation bound. -/
theorem price_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    price p S k c ≤ 6000000*((Codec.source S).length+S.nnz+1)*
      (NormalizeSource.frontendWidth p S k c+1)^2 := by
  let N := (Codec.source S).length
  let m := S.nnz
  let P := Realization.binaryCoefficientPrecision m k c
  let D := NormalizeSource.frontendWidth p S k c
  let A := (D+1)^2
  have hn : S.n ≤ m := Source.dimension_le_nnz S hp.1
  have hbase : m.size+MagnitudeMax.inputWidth p S+3 ≤ D := by
    dsimp [D,NormalizeSource.frontendWidth,m]
    nlinarith
  have hD : 36 ≤ D := by dsimp [D,NormalizeSource.frontendWidth]; nlinarith
  have hDA : D ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P,Realization.binaryCoefficientPrecision,D,NormalizeSource.frontendWidth,m]
    nlinarith
  have hPsize : P.size ≤ P := by
    simpa only [WordLength.countBits_eq,Nat.size_eq_bits_len] using WordLength.countBits_length P
  have hsize : m.size+P.size+10 ≤ 3*(D+1) := by omega
  have hsquare : (m.size+P.size+10)^2 ≤ 9*A := by
    have hh := Nat.pow_le_pow_left hsize 2
    dsimp [A]
    nlinarith
  have hi := Initialize.price_bound S.n m P hn
  have hi' : Initialize.price S.n m P ≤ 450000*(N+m+1)*A := by
    have hh := Nat.mul_le_mul_left (50000*(S.n+1)) hsquare
    have hlarge : (S.n+1)*A ≤ (N+m+1)*A := Nat.mul_le_mul_right _ (by omega)
    nlinarith only [hi,hh,hlarge]
  have har := archive_length S P hn
  have har' : 4*(archive S P).length+6 ≤ 26*(N+m+1)*A := by
    have hunit : 4*m.size+P+3 ≤ 6*A := by omega
    have hmA := Nat.mul_le_mul_left m hunit
    have htotal : (m+1)*A ≤ (N+m+1)*A := Nat.mul_le_mul_right _ (by omega)
    change (archive S P).length ≤ m*(4*m.size+P+3) at har
    nlinarith only [har,hmA,htotal,hA]
  have hnrm := NormalizeSource.price_bound p S hp k c
  change NormalizeSource.price p S k c ≤ 4000000*(N+m+1)*A at hnrm
  change NormalizeSource.price p S k c+Initialize.price S.n m P+
    (4*(archive S P).length+6) ≤ 6000000*(N+m+1)*A
  nlinarith only [hnrm,hi',har']

end Maxwell.Cost.SourceCircuit.Preparation
