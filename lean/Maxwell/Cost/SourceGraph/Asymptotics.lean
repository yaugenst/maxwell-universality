import Maxwell.Cost.SourceGraph.Positive
import Maxwell.Cost.SourceGraph.Retain.Bounds
import Maxwell.Cost.SourceSquare.Asymptotics

namespace Maxwell.Cost.SourceGraph.Positive
open SourceCircuit

/-- A fixed constant for all actual source-to-graph preprocessing stages. -/
def graphFactor : ℕ := 13000000 + 9010 +
  9*(3000*8^PositiveGraph.Metadata.statements.length+100) + 659200000 +
  4*(3000*8^Retain.statements.length)+160 + 64125000000

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem totalBudget_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    totalBudget p S k c ≤ graphFactor*((Codec.source S).length+S.nnz+1)*
      (NormalizeSource.frontendWidth p S k c+1)^3 := by
  let m := S.nnz
  let P := Realization.binaryCoefficientPrecision m k c
  let D := NormalizeSource.frontendWidth p S k c
  let F := D+1
  let N := (Codec.source S).length+m+1
  let Q := N*F^3
  let W := width S P
  let d := dimension S P
  let K := count S P
  let MC := 3000*8^PositiveGraph.Metadata.statements.length+100
  let RC := 3000*8^Retain.statements.length
  have hbase : m.size+MagnitudeMax.inputWidth p S+3 ≤ D := by
    dsimp [D,NormalizeSource.frontendWidth,m]; nlinarith
  have hP : P+1 ≤ D := by
    dsimp [P,Realization.binaryCoefficientPrecision,D,NormalizeSource.frontendWidth,m]; nlinarith
  have hPpos : 1 ≤ P := by dsimp [P,Realization.binaryCoefficientPrecision]; omega
  have hD : 36 ≤ D := by dsimp [D,NormalizeSource.frontendWidth]; nlinarith
  have hPsize : P.size ≤ P := by
    simpa only [WordLength.countBits_eq,Nat.size_eq_bits_len] using WordLength.countBits_length P
  have hW : W+6 ≤ 3*F := by
    dsimp [W,width,InitializeMetadata.width,InitializeMetadata.exponent,F]
    change 4+m.size+P.size+1+6 ≤ 3*(D+1)
    omega
  have hsrc : NormalizeSource.sourceWidth p S P+2 ≤ 2*F := by
    dsimp [NormalizeSource.sourceWidth,F]
    simp only [Nat.size_eq_bits_len]
    change MagnitudeMax.inputWidth p S+m.size+P+1+2 ≤ 2*(D+1)
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hF : 1 ≤ F := by dsimp [F]; omega
  have hmN : m ≤ N := by dsimp [N]; omega
  have hmNF := Nat.mul_le_mul_right F hmN
  have hd := Logical.sourceCircuit_size S P (Source.dimension_le_nnz S hp.1)
  change d ≤ 6*m*(P+1) at hd
  have hdF : d ≤ 6*N*F := by
    have hh := Nat.mul_le_mul_left (6*m) (show P+1 ≤ F by dsimp [F]; omega)
    nlinarith only [hd,hh,hmNF]
  have hK := Logical.sourceSquareEntries_length_le S P
  change K ≤ 3*d at hK
  have hKF : K ≤ 18*N*F := by nlinarith only [hK,hdF]
  have hNF : 1 ≤ N*F := by simpa using Nat.mul_le_mul hN hF
  have hF2 : F ≤ F^2 := by nlinarith only [hF]
  have hF3 : F^2 ≤ F^3 := by
    have hh := Nat.mul_le_mul_left F hF2
    nlinarith only [hh]
  have hNF2 : N*F^2 ≤ Q := Nat.mul_le_mul_left N hF3
  have hF2Q : F^2 ≤ Q := by
    have hh := Nat.mul_le_mul_right (F^2) hN
    nlinarith only [hh,hNF2]
  have hFQ : F ≤ Q := hF2.trans hF2Q
  have hNQ : N ≤ Q := by
    have hh := Nat.mul_le_mul_left N (show 1 ≤ F^3 from Nat.one_le_pow _ _ hF)
    simpa [Q] using hh
  have hQ : 1 ≤ Q := hN.trans hNQ
  have hW2 : (W+6)^2 ≤ 9*F^2 := by
    have hh := Nat.pow_le_pow_left hW 2
    nlinarith only [hh]
  have hroom : d < 2^W := by
    have hm := Nat.lt_size_self m
    have hp' := Nat.lt_size_self P
    have hprod : m*P < 2^m.size*2^P.size := by
      have hpos : 0 < 2^m.size := by positivity
      nlinarith
    have hsmall : d ≤ 12*(m*P) := by nlinarith only [hd,hPpos]
    have hpos : 0 < 2^m.size*2^P.size := by positivity
    dsimp [W,width,InitializeMetadata.width,InitializeMetadata.exponent]
    change d < 2^(4+m.size+P.size+1)
    simp only [pow_add]
    norm_num
    nlinarith only [hprod,hsmall,hpos]
  have hmeta := PositiveGraph.Metadata.price_bound W d K hroom (Prepare.count_bound S P hroom)
  change PositiveGraph.Metadata.price W d K ≤ MC*(W+6)^2 at hmeta
  have hmetaQ : PositiveGraph.Metadata.price W d K ≤ 9*MC*Q := by
    have hh := Nat.mul_le_mul_left MC hW2
    have hl := Nat.mul_le_mul_left (9*MC) hF2Q
    nlinarith only [hmeta,hh,hl]
  have hcount : K*(66*W+12*(W+3)+89)+10 ≤ 9010*Q := by
    have hw : 66*W+12*(W+3)+89 ≤ 500*F := by omega
    have hh := Nat.mul_le_mul hKF hw
    have hl := Nat.mul_le_mul_left 9000 hNF2
    nlinarith only [hh,hl,hQ]
  have hprepare : Prepare.suffixPrice S P ≤ (9010+9*MC)*Q := by
    change K*(66*W+12*(W+3)+89)+10+PositiveGraph.Metadata.price W d K ≤ _
    nlinarith only [hcount,hmetaQ]
  have hinit : Initialized.initializationPrice S P ≤ 659200000*Q := by
    have hf : 4*K+(2*d+K)+1 ≤ 103*N*F := by nlinarith only [hKF,hdF,hNF]
    have hw : 2*W+12+2 ≤ 8*F := by omega
    have hw2 : (2*W+12+2)^2 ≤ 64*F^2 := by
      have hh := Nat.pow_le_pow_left hw 2
      nlinarith only [hh]
    have hh := Nat.mul_le_mul hf hw2
    change 100000*(4*K+(2*d+K)+1)*(2*W+12+2)^2 ≤ _
    dsimp [Q]
    nlinarith only [hh]
  have hretain : Retain.price S P ≤ (4*RC+160)*Q := by
    have hr := Retain.numericPrice_bound p S hp P
    change Retain.numericPrice S P ≤ RC*(NormalizeSource.sourceWidth p S P+2)^2 at hr
    have hsrc2 : (NormalizeSource.sourceWidth p S P+2)^2 ≤ 4*F^2 := by
      have hh := Nat.pow_le_pow_left hsrc 2
      nlinarith only [hh]
    have hn := Nat.mul_le_mul_left RC hsrc2
    have hl := Nat.mul_le_mul_left (4*RC) hF2Q
    have hdim : 31*W+35 ≤ 128*Q := by omega
    have hbytes := Retain.rhs_length S
    have hclone : 15*(LogRats.records (List.ofFn S.source)).length+17 ≤ 32*Q := by
      have hb : (Codec.source S).length+1 ≤ N := by dsimp [N]; omega
      omega
    change Retain.numericPrice S P+(31*W+35)+
      (15*(LogRats.records (List.ofFn S.source)).length+17) ≤ _
    nlinarith only [hr,hn,hl,hdim,hclone]
  have hpass : passBudget S P ≤ 64125000000*Q := by
    have hk : K+1 ≤ 19*N*F := by nlinarith only [hKF,hNF]
    have hw : (W+1)^2 ≤ 9*F^2 := by
      have hh := Nat.pow_le_pow_left (show W+1 ≤ W+6 by omega) 2
      omega
    have hh := Nat.mul_le_mul hk hw
    change 375000000*(K+1)*(W+1)^2 ≤ _
    dsimp [Q]
    nlinarith only [hh]
  have hsquare : SourceSquare.totalBudget p S k c = 13000000*Q := by
    dsimp [SourceSquare.totalBudget,Q,N,F,D,m]
    ring
  rw [totalBudget,Retained.totalBudget,Initialized.totalBudget,Prepare.totalBudget,hsquare]
  change 13000000*Q+Prepare.suffixPrice S P+Initialized.initializationPrice S P+
    Retain.price S P+passBudget S P ≤ graphFactor*N*F^3
  have hh : 13000000*Q+Prepare.suffixPrice S P+Initialized.initializationPrice S P+
      Retain.price S P+passBudget S P ≤
      (13000000+(9010+9*MC)+659200000+(4*RC+160)+64125000000)*Q := by
    nlinarith only [hprepare,hinit,hretain,hpass]
  calc
    _ ≤ _ := hh
    _ = graphFactor*N*F^3 := by dsimp only [Q,MC,RC,graphFactor]; ring

noncomputable def runtimeFactor (p : Source.Parameters) (k c : ℕ) : ℝ :=
  graphFactor*SourceSquare.sourceLogFactor p*(SourceSquare.widthLogFactor p k c)^3

theorem runtimeFactor_pos (p : Source.Parameters) (k c : ℕ) : 0 < runtimeFactor p k c := by
  have ha := SourceSquare.logUnit_pos
  have hb := p.inputBitFactor_pos
  unfold runtimeFactor SourceSquare.sourceLogFactor SourceSquare.widthLogFactor graphFactor
  positivity

/-- The complete actual source-to-positive-graph construction obeys the
same uniform m log(m+2)^4 bound as its sparse-source frontend. -/
theorem totalBudget_polylog (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) :
    (totalBudget p S k c : ℝ) ≤
      runtimeFactor p k c*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2)^4 := by
  have hn := SourceSquare.sourceLength_log_bound p S hp hm
  have hd := SourceSquare.frontendWidth_log_bound p S k c hm
  have hdpow := pow_le_pow_left₀ (Nat.cast_nonneg (NormalizeSource.frontendWidth p S k c+1)) hd 3
  have hlog : 0 ≤ Real.log ((S.nnz : ℝ)+2) := Real.log_nonneg (by
    have h := Nat.cast_nonneg S.nnz (α := ℝ); linarith)
  have hprod := mul_le_mul hn hdpow
    (by positivity : (0:ℝ) ≤ ((NormalizeSource.frontendWidth p S k c+1 : ℕ):ℝ)^3)
    (by
      have := SourceSquare.logUnit_pos
      have := p.inputBitFactor_pos
      unfold SourceSquare.sourceLogFactor
      positivity : (0:ℝ) ≤ SourceSquare.sourceLogFactor p*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2))
  have hscaled := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg graphFactor (α := ℝ))
  have hb : (totalBudget p S k c : ℝ) ≤
      (graphFactor : ℝ)*(((Codec.source S).length+S.nnz+1 : ℕ):ℝ)*
      ((NormalizeSource.frontendWidth p S k c+1 : ℕ):ℝ)^3 := by
    exact_mod_cast totalBudget_bound p S hp k c
  apply hb.trans
  convert hscaled using 1 <;> (try dsimp only [runtimeFactor]) <;> ring

theorem exists_uniform_polylog_bound (p : Source.Parameters) (k c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Source.SparseSystem, Source.Promises p S → 2 ≤ S.nnz →
      (totalBudget p S k c : ℝ) ≤ C*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2)^4 :=
  ⟨runtimeFactor p k c,runtimeFactor_pos p k c,fun S hp hm => totalBudget_polylog p S hp hm k c⟩

end Maxwell.Cost.SourceGraph.Positive
