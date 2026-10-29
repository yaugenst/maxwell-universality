import Maxwell.Cost.SourceCircuit.CompileSource.Run
import Maxwell.Logical.SourceCircuit

namespace Maxwell.Cost.SourceSquare
open SourceCircuit

def emissionBudget (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  1000*((Logical.sourceCircuit S p).size+1)*(InitializeMetadata.width S.nnz p+1)

theorem emissionBudget_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) :
    emissionBudget S p ≤ 7000*(S.nnz+1)*(p+1)*(InitializeMetadata.width S.nnz p+5) := by
  have h := Logical.sourceCircuit_size S p hn
  have hb : (Logical.sourceCircuit S p).size+1 ≤ 7*(S.nnz+1)*(p+1) := by nlinarith
  have hm := Nat.mul_le_mul hb
    (show InitializeMetadata.width S.nnz p+1 ≤ InitializeMetadata.width S.nnz p+5 by omega)
  dsimp [emissionBudget]
  nlinarith only [hm]

noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  13000000*((Codec.source S).length+S.nnz+1)*(NormalizeSource.frontendWidth p S k c+1)^3

theorem total_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    CompileSource.totalBudget p S k c+emissionBudget S (Realization.binaryCoefficientPrecision S.nnz k c) ≤
      totalBudget p S k c := by
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
  have hemit := emissionBudget_bound S P (Source.dimension_le_nnz S hp.1)
  have hmul := Nat.mul_le_mul_left (7000*(m+1)) (Nat.mul_le_mul hP hw)
  have hmono : (m+1)*D*(D+1) ≤ ((Codec.source S).length+m+1)*(D+1)^3 := by
    have hh := Nat.mul_le_mul (show m+1 ≤ (Codec.source S).length+m+1 by omega)
      (show D ≤ (D+1)^2 by nlinarith)
    have ht := Nat.mul_le_mul_right (D+1) hh
    nlinarith only [ht]
  change emissionBudget S P ≤ 7000*(m+1)*(P+1)*(InitializeMetadata.width m P+5) at hemit
  change 12000000*((Codec.source S).length+m+1)*(D+1)^3+emissionBudget S P ≤
    13000000*((Codec.source S).length+m+1)*(D+1)^3
  nlinarith only [hemit,hmul,hmono]

end Maxwell.Cost.SourceSquare
