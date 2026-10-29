import Maxwell.Cost.SourceSquare.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Maxwell.Cost.SourceSquare

noncomputable def logUnit : ℝ := (Real.log 2)⁻¹
noncomputable def sourceLogFactor (p : Source.Parameters) : ℝ :=
  40*logUnit+8*p.inputBitFactor
noncomputable def widthLogFactor (p : Source.Parameters) (k c : ℕ) : ℝ :=
  (k+c+12 : ℕ)*(9*logUnit+p.inputBitFactor)+logUnit
noncomputable def runtimeFactor (p : Source.Parameters) (k c : ℕ) : ℝ :=
  13000000*sourceLogFactor p*(widthLogFactor p k c)^3

theorem logUnit_pos : 0 < logUnit := inv_pos.mpr (Real.log_pos (by norm_num))

theorem logUnit_log_bound (m : ℕ) (hm : 2 ≤ m) :
    1 ≤ logUnit*Real.log ((m : ℝ)+2) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log 2 ≤ Real.log ((m : ℝ)+2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlog logUnit_pos.le
  simpa [logUnit,ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))] using hh

theorem size_log_bound (m : ℕ) (hm : 2 ≤ m) :
    (m.size : ℝ) ≤ 2*logUnit*Real.log ((m : ℝ)+2) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsize : m.size = m.log2+1 := by
    rw [← Codec.unsignedBitLength_eq_size]
    simp [unsignedBitLength,show m ≠ 0 by omega]
  have hlog := Real.log2_le_logb m
  rw [Real.logb] at hlog
  have hmono : Real.log (m : ℝ) ≤ Real.log ((m : ℝ)+2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hmono logUnit_pos.le
  have hone := logUnit_log_bound m hm
  rw [hsize]
  push_cast
  dsimp [logUnit] at hmul hone ⊢
  rw [div_eq_mul_inv] at hlog
  nlinarith only [hlog,hmul,hone]

theorem coefficient_log_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 2 ≤ S.nnz) :
    (Nat.ceil (Source.bitBudget p S) : ℝ) ≤
      (p.inputBitFactor+logUnit)*Real.log ((S.nnz : ℝ)+2) := by
  have hlog : 0 ≤ Real.log ((S.nnz : ℝ)+2) := Real.log_nonneg (by have h := Nat.cast_nonneg S.nnz (α := ℝ); linarith)
  have hbudget : 0 ≤ Source.bitBudget p S := by
    dsimp [Source.bitBudget]
    rw [add_comm 2]
    exact mul_nonneg p.inputBitFactor_pos.le hlog
  have hceil := (Nat.ceil_lt_add_one hbudget).le
  have hone := logUnit_log_bound S.nnz hm
  dsimp [Source.bitBudget] at hceil
  rw [add_comm 2] at hceil
  dsimp [Source.bitBudget]
  rw [add_comm 2]
  nlinarith only [hceil,hone]

theorem inputWidth_log_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 2 ≤ S.nnz) :
    (MagnitudeMax.inputWidth p S : ℝ) ≤
      (4*logUnit+p.inputBitFactor)*Real.log ((S.nnz : ℝ)+2) := by
  have hs := size_log_bound S.nnz hm
  have hb := coefficient_log_bound p S hm
  have hone := logUnit_log_bound S.nnz hm
  simp only [MagnitudeMax.inputWidth,Codec.unsignedBitLength_eq_size,Nat.cast_add,Nat.cast_one]
  nlinarith only [hs,hb,hone]

theorem frontendWidth_log_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (k c : ℕ) (hm : 2 ≤ S.nnz) :
    ((NormalizeSource.frontendWidth p S k c+1 : ℕ) : ℝ) ≤
      widthLogFactor p k c*Real.log ((S.nnz : ℝ)+2) := by
  have hs := size_log_bound S.nnz hm
  have hb := inputWidth_log_bound p S hm
  have hone := logUnit_log_bound S.nnz hm
  have base : (S.nnz.size : ℝ)+(MagnitudeMax.inputWidth p S : ℝ)+3 ≤
      (9*logUnit+p.inputBitFactor)*Real.log ((S.nnz : ℝ)+2) := by
    nlinarith only [hs,hb,hone]
  have hmul := mul_le_mul_of_nonneg_left base (Nat.cast_nonneg (k+c+12) : (0:ℝ)≤_)
  simp only [NormalizeSource.frontendWidth,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    widthLogFactor] at hmul ⊢
  nlinarith only [hmul,hone]

set_option maxHeartbeats 600000 in
theorem sourceLength_log_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) :
    (((Codec.source S).length+S.nnz+1 : ℕ) : ℝ) ≤
      sourceLogFactor p*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2) := by
  have hn := Codec.promised_source_length_le p S hp
  rw [Codec.unsignedBitLength_eq_size] at hn
  have hn' : ((Codec.source S).length : ℝ) ≤
      3*(2*(S.nnz.size : ℝ)+1)+(S.nnz : ℝ)*
        (4*(S.nnz.size : ℝ)+8*(Nat.ceil (Source.bitBudget p S) : ℝ)+4) := by exact_mod_cast hn
  have hs := size_log_bound S.nnz hm
  have hb := coefficient_log_bound p S hm
  have hone := logUnit_log_bound S.nnz hm
  have hm' : (2 : ℝ) ≤ S.nnz := by exact_mod_cast hm
  have ha : 0 ≤ logUnit*Real.log ((S.nnz : ℝ)+2) := by linarith
  have hbsize : 4*(S.nnz.size : ℝ)+8*(Nat.ceil (Source.bitBudget p S) : ℝ)+4 ≤
      (20*logUnit+8*p.inputBitFactor)*Real.log ((S.nnz : ℝ)+2) := by
    nlinarith only [hs,hb,hone]
  have hmul := mul_le_mul_of_nonneg_left hbsize (Nat.cast_nonneg S.nnz : (0:ℝ)≤_)
  have hmone := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg S.nnz : (0:ℝ)≤_)
  have hbase : 3*(2*(S.nnz.size : ℝ)+1) ≤ 15*logUnit*Real.log ((S.nnz : ℝ)+2) := by
    nlinarith only [hs,hone]
  have hlarge : 16*logUnit*Real.log ((S.nnz : ℝ)+2) ≤
      19*(S.nnz : ℝ)*logUnit*Real.log ((S.nnz : ℝ)+2) := by
    nlinarith only [hm',ha]
  simp only [Nat.cast_add,Nat.cast_one]
  dsimp [sourceLogFactor]
  nlinarith only [hn',hmul,hmone,hbase,hlarge,hone]

theorem runtimeFactor_pos (p : Source.Parameters) (k c : ℕ) : 0 < runtimeFactor p k c := by
  have ha := logUnit_pos
  have hb := p.inputBitFactor_pos
  unfold runtimeFactor sourceLogFactor widthLogFactor
  positivity

/-- The actual source compiler and sparse emitter have a uniform
m log(m+2)^4 bit-operation bound under the original source promises. -/
theorem totalBudget_polylog (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) :
    (totalBudget p S k c : ℝ) ≤
      runtimeFactor p k c*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2)^4 := by
  have hn := sourceLength_log_bound p S hp hm
  have hd := frontendWidth_log_bound p S k c hm
  have hdpow := pow_le_pow_left₀ (Nat.cast_nonneg (NormalizeSource.frontendWidth p S k c+1)) hd 3
  have hlog : 0 ≤ Real.log ((S.nnz : ℝ)+2) := Real.log_nonneg (by
    have h := Nat.cast_nonneg S.nnz (α := ℝ); linarith)
  have hprod := mul_le_mul hn hdpow
    (by positivity : (0:ℝ) ≤ ((NormalizeSource.frontendWidth p S k c+1 : ℕ):ℝ)^3)
    (by
      have := logUnit_pos
      have := p.inputBitFactor_pos
      unfold sourceLogFactor
      positivity : (0:ℝ) ≤ sourceLogFactor p*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2))
  have hscaled := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤13000000)
  convert hscaled using 1 <;> simp only [totalBudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,runtimeFactor] <;> ring

theorem exists_uniform_polylog_bound (p : Source.Parameters) (k c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Source.SparseSystem, Source.Promises p S → 2 ≤ S.nnz →
      (totalBudget p S k c : ℝ) ≤ C*(S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2)^4 :=
  ⟨runtimeFactor p k c,runtimeFactor_pos p k c,fun S hp hm => totalBudget_polylog p S hp hm k c⟩

end Maxwell.Cost.SourceSquare
