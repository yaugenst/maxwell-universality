import Maxwell.Cost.SourceCircuit.ArithmeticPrelude

namespace Maxwell.Cost.SourceCircuit.ArithmeticPrelude

theorem leafWords_flatten_length (S : Source.SparseSystem) (p : ℕ) :
    (leafWords S p).flatten.length =
      AllocationPass.occurrences (AllocateSource.records S p)*InitializeMetadata.width S.nnz p := by
  have hgen (ids : List ℕ) (W : ℕ) :
      (ids.flatMap (fixedWidth W)).length = ids.length*W := by
    induction ids with
    | nil => simp
    | cons i ids ih => simp [fixedWidth_length,ih,Nat.add_mul,Nat.add_comm]
  change (((AllocateSource.bank S p).outputs.map Fin.val).flatMap
    (fixedWidth (InitializeMetadata.width S.nnz p))).length = _
  rw [hgen,List.length_map,(AllocateSource.bank S p).output_count,
    AllocationPass.requests_length]

theorem price_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) :
    price S.nnz (Preparation.archive S p) (leafWords S p).flatten (flags S) ≤
      100*(S.nnz+1)*(p+1)*(InitializeMetadata.width S.nnz p+5) := by
  let W := InitializeMetadata.width S.nnz p
  have har := Preparation.archive_length S p hn
  have hl := AllocateSource.records_occurrences S p
  have hmul := Nat.mul_le_mul_right W hl
  have hms : S.nnz.size ≤ W := by dsimp [W,InitializeMetadata.width,InitializeMetadata.exponent]; omega
  rw [price,leafWords_flatten_length,flags_length]
  rw [Nat.size_eq_bits_len]
  change _ ≤ 100*(S.nnz+1)*(p+1)*(W+5)
  have hsize : 21*S.nnz.size ≤ 21*W := Nat.mul_le_mul_left _ hms
  have hrow : 4*S.nnz.size+p+3 ≤ 4*W+p+3 := by omega
  have hrowmul := Nat.mul_le_mul_left S.nnz hrow
  nlinarith only [har,hmul,hsize,hrowmul]

theorem sourcePrice_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    sourcePrice p S k c ≤ 11000000*((Codec.source S).length+S.nnz+1)*
      (NormalizeSource.frontendWidth p S k c+1)^3 := by
  let m := S.nnz
  let P := Realization.binaryCoefficientPrecision m k c
  let D := NormalizeSource.frontendWidth p S k c
  have hbase : m.size+MagnitudeMax.inputWidth p S+3 ≤ D := by
    dsimp [D,NormalizeSource.frontendWidth,m]; nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P,Realization.binaryCoefficientPrecision,D,NormalizeSource.frontendWidth,m]; nlinarith
  have hD : 36 ≤ D := by dsimp [D,NormalizeSource.frontendWidth]; nlinarith
  have hPsize : P.size ≤ P := by
    simpa only [WordLength.countBits_eq,Nat.size_eq_bits_len] using WordLength.countBits_length P
  have hw : InitializeMetadata.width m P+5 ≤ 3*(D+1) := by
    dsimp [InitializeMetadata.width,InitializeMetadata.exponent]; omega
  have hq := price_bound S P (Source.dimension_le_nnz S hp.1)
  have hscale := Nat.mul_le_mul hP hw
  have hmul := Nat.mul_le_mul_left (100*(m+1)) hscale
  have hmono : (m+1)*(D+1)^2 ≤ ((Codec.source S).length+m+1)*(D+1)^3 := by
    have hN : m+1 ≤ (Codec.source S).length+m+1 := by omega
    have hdegree : (D+1)^2 ≤ (D+1)^3 := by nlinarith
    exact Nat.mul_le_mul hN hdegree
  have ha := AllocateSource.price_bound p S hp k c
  change price m (Preparation.archive S P) (leafWords S P).flatten (flags S) ≤
    100*(m+1)*(P+1)*(InitializeMetadata.width m P+5) at hq
  change AllocateSource.price p S k c ≤ 10000000*((Codec.source S).length+m+1)*(D+1)^3 at ha
  change AllocateSource.price p S k c+price m (Preparation.archive S P) (leafWords S P).flatten (flags S) ≤
    11000000*((Codec.source S).length+m+1)*(D+1)^3
  nlinarith only [hq,hmul,hmono,ha]

end Maxwell.Cost.SourceCircuit.ArithmeticPrelude
