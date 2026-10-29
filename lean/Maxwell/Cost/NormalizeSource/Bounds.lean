import Maxwell.Cost.NormalizeSource
import Maxwell.Cost.MagnitudeMax.BothBound

namespace Maxwell.Cost.NormalizeSource
set_option maxHeartbeats 1000000

noncomputable def frontendWidth (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  (k+c+12)*(S.nnz.size+MagnitudeMax.inputWidth p S+3)

/-- The actual frontend cost is linear in source bytes and stored entries,
with a quadratic factor in their explicit binary precision budget. -/
theorem frontendPrice_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    frontendPrice p S k c ≤ 2000000*((Codec.source S).length+S.nnz+1)*
      (frontendWidth p S k c+1)^2 := by
  let N := (Codec.source S).length
  let m := S.nnz
  let B := MagnitudeMax.inputWidth p S
  let D := frontendWidth p S k c
  let A := (D+1)^2
  let P := Realization.binaryCoefficientPrecision m k c
  have hn : S.n.size ≤ m.size := Nat.size_le_size (Source.dimension_le_nnz S hp.1)
  have hbase : m.size+B+3 ≤ D := by dsimp [D, frontendWidth, m, B]; nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P, Realization.binaryCoefficientPrecision, D, frontendWidth, m, B]
    nlinarith
  have hD : 36 ≤ D := by dsimp [D, frontendWidth]; nlinarith
  have hDA : D ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hB2 : (B+2)^2 ≤ A := by
    dsimp [A]
    exact Nat.pow_le_pow_left (by omega) 2
  have hfront := MagnitudeMax.Both.price_le S B
  have hcoeff : (B+2)^2+2*S.n.bits.length+S.nnz.bits.length+1 ≤ 5*A := by
    simp only [Nat.size_eq_bits_len]
    change (B+2)^2+2*S.n.size+m.size+1 ≤ _
    omega
  have hfront' : MagnitudeMax.Both.price S B ≤ 65000*(N+m+1)*A := by
    calc
      _ ≤ 13000*(N+1)*(5*A) := hfront.trans (Nat.mul_le_mul_left _ hcoeff)
      _ ≤ 65000*(N+m+1)*A := by nlinarith
  have hmeta : SourceMetadata.costBound m B k c ≤ 4000*(N+m+1)*A := by
    change 4000*D^2 ≤ _
    have hsq : D^2 ≤ A := Nat.pow_le_pow_left (by omega) 2
    have hlarge : 1 ≤ N+m+1 := by omega
    nlinarith
  have hrep : SourceReplay.price (Codec.sourceRecord S) ≤ 56*(N+m+1)*A := by
    have hh := SourceReplay.price_le (Codec.sourceRecord S)
    rw [ParseSource.source_wire] at hh
    change _ ≤ 11*N+45 at hh
    have hlarge : N+1 ≤ (N+m+1)*A := by nlinarith
    nlinarith
  have hwidth : sourceWidth p S P+2 ≤ 3*(D+1) := by
    dsimp [sourceWidth]
    simp only [Nat.size_eq_bits_len]
    change B+m.size+P+1+2 ≤ _
    omega
  have hw2 : (sourceWidth p S P+2)^2 ≤ 9*A := by
    have hh := Nat.pow_le_pow_left hwidth 2
    dsimp [A]
    nlinarith
  have hmatrix : matrixPassPrice S.n (Codec.sourceRecord S).entries (sourceWidth p S P) ≤
      1200000*(N+m+1)*A := by
    have hread : 21*S.n.bits.length+16+21*m.bits.length+16 ≤ 74*A := by
      simp only [Nat.size_eq_bits_len]
      omega
    have hcounter : 13*m.bits.length+15 ≤ 28*A := by
      simp only [Nat.size_eq_bits_len]
      omega
    have hcounter' := Nat.mul_le_mul_left (m+1) hcounter
    have hbody := Nat.mul_le_mul_left (m*130000) hw2
    have ha : A ≤ (N+m+1)*A := by nlinarith
    have hma : m*A ≤ (N+m+1)*A := by nlinarith
    have hm1a : (m+1)*A ≤ (N+m+1)*A := by nlinarith
    simp only [matrixPassPrice, loopPrice, Codec.sourceRecord,
      List.length_map, List.length_attach, Codec.sourceEntries_length]
    change 21*S.n.bits.length+16+21*m.bits.length+16+
      ((m+1)*(13*m.bits.length+15)+m*(130000*(sourceWidth p S P+2)^2)) ≤ _
    nlinarith only [hread, hcounter', hbody, ha, hma, hm1a]
  change MagnitudeMax.Both.price S B+SourceMetadata.costBound m B k c+
      SourceReplay.price (Codec.sourceRecord S)+
      matrixPassPrice S.n (Codec.sourceRecord S).entries (sourceWidth p S P) ≤ _
  change _ ≤ 2000000*(N+m+1)*A
  nlinarith only [hfront', hmeta, hrep, hmatrix]

/-- The complete normalization execution, including every RHS coordinate,
is linear in the canonical input bytes and sparse entry count up to the
explicit quadratic binary-precision factor. -/
theorem price_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    price p S k c ≤ 4000000*((Codec.source S).length+S.nnz+1)*
      (frontendWidth p S k c+1)^2 := by
  let N := (Codec.source S).length
  let m := S.nnz
  let B := MagnitudeMax.inputWidth p S
  let D := frontendWidth p S k c
  let A := (D+1)^2
  let P := Realization.binaryCoefficientPrecision m k c
  have hn : S.n ≤ m := Source.dimension_le_nnz S hp.1
  have hnsize : S.n.size ≤ m.size := Nat.size_le_size hn
  have hbase : m.size+B+3 ≤ D := by dsimp [D, frontendWidth, m, B]; nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P, Realization.binaryCoefficientPrecision, D, frontendWidth, m, B]
    nlinarith
  have hDA : D ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hwidth : sourceWidth p S P+2 ≤ 3*(D+1) := by
    dsimp [sourceWidth]
    simp only [Nat.size_eq_bits_len]
    change B+m.size+P+1+2 ≤ _
    omega
  have hw2 : (sourceWidth p S P+2)^2 ≤ 9*A := by
    have hh := Nat.pow_le_pow_left hwidth 2
    dsimp [A]
    nlinarith
  have hsum : (sourceWidth p S P+2)^2+S.n.bits.length+1 ≤ 11*A := by
    simp only [Nat.size_eq_bits_len]
    omega
  have hr := Rhs.price_le (List.ofFn S.source) (sourceWidth p S P)
  simp only [List.length_ofFn] at hr
  have hr' : Rhs.price (List.ofFn S.source) (sourceWidth p S P) ≤
      1400000*(N+m+1)*A := by
    have hh := Nat.mul_le_mul_left (120100*(S.n+1)) hsum
    have hlarge : (S.n+1)*A ≤ (N+m+1)*A := Nat.mul_le_mul_right _ (by omega)
    nlinarith only [hr, hh, hlarge]
  have hf := frontendPrice_bound p S hp k c
  change frontendPrice p S k c ≤ 2000000*(N+m+1)*A at hf
  change frontendPrice p S k c+Rhs.price (List.ofFn S.source) (sourceWidth p S P) ≤
    4000000*(N+m+1)*A
  nlinarith only [hf, hr']

end Maxwell.Cost.NormalizeSource
