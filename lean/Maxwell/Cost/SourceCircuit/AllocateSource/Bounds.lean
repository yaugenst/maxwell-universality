import Maxwell.Cost.SourceCircuit.AllocateSource

namespace Maxwell.Cost.SourceCircuit.AllocateSource

theorem occurrenceCost_bound (W : ℕ) (index clock : List Bool)
    (hi : index.length = W) (hc : clock.length = W) :
    occurrenceCost W.bits index [] clock ≤ 20000*(W+5)^2 := by
  have hbits : W.bits.length ≤ W := by
    simpa only [WordLength.countBits_eq] using WordLength.countBits_length W
  simp only [occurrenceCost,allocationCost,BankArray.costCap,ArrayAccess.costCap,
    addressValue_bits,List.length_nil,hi,hc]
  have hsum : W.bits.length+W+0+5 ≤ 2*(W+5) := by omega
  have hsquare := Nat.pow_le_pow_left hsum 2
  nlinarith only [hbits,hsquare]

theorem recordCost_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz)
    (r : AllocationPass.Record S.n) (hr : r ∈ records S p) :
    AllocationPass.recordCost (wordWidth S p) [] (clock S p) r ≤
      30000*(p+1)*(InitializeMetadata.width S.nnz p+5)^2 := by
  let W := InitializeMetadata.width S.nnz p
  have hc : (clock S p).length = W := clock_length S p
  have hp := records_precision S p r hr
  have hrfit : r.row.bits.length ≤ W := by
    have ht := Nat.size_le_size (show r.row ≤ S.nnz by have := records_row S p r hr; omega)
    simp only [W,InitializeMetadata.width,InitializeMetadata.exponent,Nat.size_eq_bits_len] at *
    omega
  have hcol : r.column.val.bits.length ≤ W := width_fit S p hn r.column
  have ho := occurrenceCost_bound W (FixedWidth.bits (clock S p).length r.column.val.bits)
    (clock S p) (by rw [FixedWidth.bits_length,hc]) hc
  have hmul := Nat.mul_le_mul_left p ho
  change p*occurrenceCost (wordWidth S p)
    (FixedWidth.bits (clock S p).length r.column.val.bits) [] (clock S p) ≤
    p*(20000*(W+5)^2) at hmul
  rw [hc] at hmul
  simp only [AllocationPass.recordCost,AllocateRecord.bound,hp,hc]
  change _ ≤ 30000*(p+1)*(W+5)^2
  have hsmall : 40*r.row.bits.length+49*r.column.val.bits.length+98*W+191 ≤
      200*(W+5)^2 := by nlinarith only [hrfit,hcol]
  have hunit : 1 ≤ (W+5)^2 := by nlinarith
  have hpunit := Nat.mul_le_mul_left (32*p) hunit
  nlinarith only [hmul,hsmall,hpunit]

private theorem maximumCost_le {n : ℕ} (width base clock : List Bool)
    (rs : List (AllocationPass.Record n)) (B : ℕ)
    (h : ∀ r ∈ rs, AllocationPass.recordCost width base clock r ≤ B) :
    AllocationPass.maximumCost width base clock rs ≤ B := by
  induction rs with
  | nil => simp [AllocationPass.maximumCost]
  | cons r rest ih =>
    exact max_le (h r (by simp)) (ih (fun t ht => h t (by simp [ht])))

theorem passPrice_bound (S : Source.SparseSystem) (p : ℕ) (hn : S.n ≤ S.nnz) :
    passPrice S p ≤ 40000*(S.nnz+1)*(p+1)*(InitializeMetadata.width S.nnz p+5)^2 := by
  let W := InitializeMetadata.width S.nnz p
  have hmax := maximumCost_le (wordWidth S p) [] (clock S p) (records S p)
    (30000*(p+1)*(W+5)^2) (recordCost_bound S p hn)
  have hmul := Nat.mul_le_mul_left S.nnz hmax
  have hm : S.nnz.bits.length ≤ W := by
    simp only [W,InitializeMetadata.width,InitializeMetadata.exponent,Nat.size_eq_bits_len]
    omega
  have hcounter : (S.nnz+1)*(13*S.nnz.bits.length+15) ≤
      28*(S.nnz+1)*(W+5)^2 := by
    have ht : 13*S.nnz.bits.length+15 ≤ 28*(W+5)^2 := by nlinarith
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (S.nnz+1) ht
  simp only [passPrice,AllocationPass.costBound,records_length]
  change _ ≤ 40000*(S.nnz+1)*(p+1)*(W+5)^2
  have hb : S.nnz*(30000*(p+1)*(W+5)^2) ≤
      (S.nnz+1)*(30000*(p+1)*(W+5)^2) := Nat.mul_le_mul_right _ (by omega)
  have hc : 28*(S.nnz+1)*(W+5)^2 ≤ 28*(S.nnz+1)*(W+5)^2*(p+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  nlinarith only [hmul,hcounter,hb,hc]

/-- Complete source preprocessing and copy allocation cost, including
address computation, copying every leaf and every countdown instruction. -/
theorem price_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    price p S k c ≤ 10000000*((Codec.source S).length+S.nnz+1)*
      (NormalizeSource.frontendWidth p S k c+1)^3 := by
  let m := S.nnz
  let P := Realization.binaryCoefficientPrecision m k c
  let D := NormalizeSource.frontendWidth p S k c
  let A := (D+1)^2
  have hbase : m.size+MagnitudeMax.inputWidth p S+3 ≤ D := by
    dsimp [D,NormalizeSource.frontendWidth,m]
    nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P,Realization.binaryCoefficientPrecision,D,NormalizeSource.frontendWidth,m]
    nlinarith
  have hD : 36 ≤ D := by dsimp [D,NormalizeSource.frontendWidth]; nlinarith
  have hPsize : P.size ≤ P := by
    simpa only [WordLength.countBits_eq,Nat.size_eq_bits_len] using WordLength.countBits_length P
  have hw : InitializeMetadata.width m P+5 ≤ 3*(D+1) := by
    dsimp [InitializeMetadata.width,InitializeMetadata.exponent]
    omega
  have hsquare : (InitializeMetadata.width m P+5)^2 ≤ 9*A := by
    have hh := Nat.pow_le_pow_left hw 2
    dsimp [A]
    nlinarith only [hh]
  have hpass := passPrice_bound S P (Source.dimension_le_nnz S hp.1)
  have hmul := Nat.mul_le_mul_left (40000*(m+1)*(P+1)) hsquare
  have hprod : (m+1)*(P+1)*A ≤ ((Codec.source S).length+m+1)*(D+1)*A := by
    exact Nat.mul_le_mul_right A (Nat.mul_le_mul (by omega) (by omega))
  have hprep := Preparation.price_bound p S hp k c
  have hdegree : ((Codec.source S).length+m+1)*A ≤
      ((Codec.source S).length+m+1)*(D+1)*A := by nlinarith
  change passPrice S P ≤ 40000*(m+1)*(P+1)*(InitializeMetadata.width m P+5)^2 at hpass
  change Preparation.price p S k c ≤ 6000000*((Codec.source S).length+m+1)*A at hprep
  change Preparation.price p S k c+passPrice S P ≤
    10000000*((Codec.source S).length+m+1)*(D+1)^3
  have he : (D+1)^3 = (D+1)*A := by dsimp [A]; ring
  rw [he]
  nlinarith only [hpass,hmul,hprod,hprep,hdegree]

end Maxwell.Cost.SourceCircuit.AllocateSource
