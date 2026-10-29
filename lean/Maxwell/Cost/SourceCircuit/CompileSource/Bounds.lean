import Maxwell.Cost.SourceCircuit.CompileSource
import Maxwell.Cost.SourceCircuit.ArithmeticPrelude.Bounds

namespace Maxwell.Cost.SourceCircuit.CompileSource

def budget (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  10000*(S.nnz+1)*(p+1)*(InitializeMetadata.width S.nnz p+5)^2

theorem coordinateBits_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) :
    ArithmeticPass.coordinateBits (AllocateSource.records S p) ≤
      2*S.nnz*InitializeMetadata.width S.nnz p := by
  let W := InitializeMetadata.width S.nnz p
  have bounds (r : AllocationPass.Record S.n) (hr : r ∈ AllocateSource.records S p) :
      r.row.bits.length+r.column.val.bits.length ≤ 2*W := by
    have hrow := AllocateSource.records_row S p r hr
    have hr := Nat.size_le_size (show r.row ≤ S.nnz by omega)
    have hc := AllocateSource.width_fit S p hn r.column
    simp only [W,InitializeMetadata.width,InitializeMetadata.exponent,Nat.size_eq_bits_len] at *
    omega
  have gen (rs : List (AllocationPass.Record S.n))
      (h : ∀ r ∈ rs, r.row.bits.length+r.column.val.bits.length ≤ 2*W) :
      ArithmeticPass.coordinateBits rs ≤ rs.length*(2*W) := by
    induction rs with
    | nil => simp [ArithmeticPass.coordinateBits]
    | cons r rs ih =>
      have hh := h r (by simp)
      have ht := ih (fun q hq => h q (by simp [hq]))
      simp only [ArithmeticPass.coordinateBits,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith
  simpa [AllocateSource.records_length,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
    gen (AllocateSource.records S p) bounds

theorem passPrice_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz)
    (hm : 1 ≤ S.nnz) (hp : 1 ≤ p) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Structured.Store) (h : AllocateSource.Result S p roots memory s) :
    passPrice S p roots memory ≤ budget S p := by
  let m := S.nnz
  let W := InitializeMetadata.width S.nnz p
  let A := (W+5)^2
  have hWA : W ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hmlen : m.bits.length ≤ W := by
    dsimp [m,W,InitializeMetadata.width,InitializeMetadata.exponent]
    rw [Nat.size_eq_bits_len]
    omega
  have hlength := AllocateSource.records_length S p
  have hflags := ArithmeticPrelude.flags_length S
  cases hrs : AllocateSource.records S p with
  | nil => rw [hrs] at hlength; simp at hlength; omega
  | cons r rs =>
    cases hfs : ArithmeticPrelude.flags S with
    | nil => rw [hfs] at hflags; simp at hflags; omega
    | cons marker fs =>
      have hv : ArithmeticPass.Valid W (r::rs) (false::fs) (ArithmeticPrelude.data S p roots memory) := by
        rw [← hrs]
        exact ArithmeticPrelude.valid S p hn hm hp roots memory s h _ (by simpa [hfs] using hflags)
      have hb := ArithmeticPass.costBound_bytes p W m.bits.length r rs fs
        (ArithmeticPrelude.data S p roots memory) hv
      have hc := coordinateBits_bound S p hn
      have hcount := List.count_le_length (a := true) (l := fs)
      have hfl : fs.length+1 = m := by simpa [hfs] using hflags
      have hrlen : (r::rs).length = m := by simpa [hrs] using hlength
      have hcoord : ArithmeticPass.coordinateBits (r::rs) ≤ 2*m*W := by simpa [hrs] using hc
      have hcounter : (m+1)*(13*m.bits.length+15) ≤ 28*(m+1)*A := by
        have hh : 13*m.bits.length+15 ≤ 28*A := by omega
        simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (m+1) hh
      have hterm : p*(158*W+246)+124*W+282 ≤ 1000*(p+1)*A := by
        have hpmul := Nat.mul_le_mul_left p (show 158*W+246 ≤ 404*A by omega)
        nlinarith only [hpmul,hWA,hA]
      have hterms := Nat.mul_le_mul_left m hterm
      have hrows := Nat.mul_le_mul_left m (show 101*W+119 ≤ 220*A by omega)
      have hboundaries := Nat.mul_le_mul (show fs.count true+1 ≤ m+1 by omega)
        (show 75*W+103 ≤ 178*A by omega)
      have hcoord' := Nat.mul_le_mul_left (80*m) hWA
      have hmA : m*A ≤ (m+1)*(p+1)*A := Nat.mul_le_mul_right _ (by nlinarith)
      have hm1A : (m+1)*A ≤ (m+1)*(p+1)*A := Nat.mul_le_mul_right _ (by nlinarith)
      have hmpA : m*(p+1)*A ≤ (m+1)*(p+1)*A := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      simp only [ArithmeticPrelude.data,List.length_nil,zero_add,hrlen] at hb
      change ArithmeticPass.costBound p W m.bits.length r rs fs
        (ArithmeticPrelude.data S p roots memory) ≤ _ at hb
      rw [passPrice,hrs,hfs]
      change ArithmeticPass.costBound p W m.bits.length r rs fs
        (ArithmeticPrelude.data S p roots memory) ≤ 10000*(m+1)*(p+1)*A
      nlinarith only [hb,hcounter,hterms,hrows,hboundaries,hcoord,hcoord',hmA,hm1A,hmpA]

noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  12000000*((Codec.source S).length+S.nnz+1)*(NormalizeSource.frontendWidth p S k c+1)^3

theorem total_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    ArithmeticPrelude.sourcePrice p S k c+budget S (Realization.binaryCoefficientPrecision S.nnz k c) ≤
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
  have hsquare : (InitializeMetadata.width m P+5)^2 ≤ 9*(D+1)^2 := by
    have hh := Nat.pow_le_pow_left hw 2; nlinarith only [hh]
  have hmul := Nat.mul_le_mul_left (10000*(m+1)) (Nat.mul_le_mul hP hsquare)
  have hmono : (m+1)*D*(D+1)^2 ≤ ((Codec.source S).length+m+1)*(D+1)^3 := by
    have hh := Nat.mul_le_mul (show m+1 ≤ (Codec.source S).length+m+1 by omega)
      (show D ≤ D+1 by omega)
    have ht := Nat.mul_le_mul_right ((D+1)^2) hh
    nlinarith only [ht]
  have hprefix := ArithmeticPrelude.sourcePrice_bound p S hp k c
  change ArithmeticPrelude.sourcePrice p S k c ≤
    11000000*((Codec.source S).length+m+1)*(D+1)^3 at hprefix
  change ArithmeticPrelude.sourcePrice p S k c+10000*(m+1)*(P+1)*(InitializeMetadata.width m P+5)^2 ≤
    12000000*((Codec.source S).length+m+1)*(D+1)^3
  nlinarith only [hmul,hmono,hprefix]

end Maxwell.Cost.SourceCircuit.CompileSource
