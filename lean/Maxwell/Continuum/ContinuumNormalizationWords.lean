import Maxwell.Continuum.ContinuumRealizationResources
import Maxwell.Continuum.RationalArithmeticWidths
import Maxwell.Logical.NormalizationBounds

/-! The normalization and final decoding scale are computed from original
sparse input words. Their widths use the source bit promise explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Logical RationalWords

def inputWordCoefficient (p : Source.Parameters) : ℕ := ⌈p.inputBitFactor⌉₊+1
def normalizationWordCoefficient (p : Source.Parameters) : ℕ := 2*inputWordCoefficient p+2

def normalizationScale (S : Source.SparseSystem) : ℚ :=
  Normalization.sourceScale S/Normalization.matrixScale S

theorem sourceBitBudget_linear (p : Source.Parameters) (S : Source.SparseSystem) :
    Source.bitBudget p S≤(inputWordCoefficient p*logSize S : ℕ) := by
  have hp : S.nnz+2≤2^logSize S :=
    (Nat.le_pow_clog (by norm_num : 1<2) (S.nnz+2)).trans
      (Nat.pow_le_pow_right (by norm_num : 0<2) (by change _≤1+_; omega))
  have hpr : (2 : ℝ)+S.nnz≤(2 : ℝ)^logSize S := by
    exact_mod_cast (show 2+S.nnz≤2^logSize S by omega)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<2+S.nnz) hpr
  rw [Real.log_pow] at hlog
  have h2 : Real.log (2 : ℝ)≤1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have hl : Real.log (2+(S.nnz : ℝ))≤logSize S := hlog.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (logSize S)))
  have hc : p.inputBitFactor≤(inputWordCoefficient p : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp only [inputWordCoefficient,Nat.cast_add,Nat.cast_one]; linarith)
  unfold Source.bitBudget
  push_cast
  exact (mul_le_mul_of_nonneg_left hl p.inputBitFactor_pos.le).trans
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))

private theorem input_width {p : Source.Parameters} {S : Source.SparseSystem} {q : ℚ}
    (h : Source.ShortRational (Source.bitBudget p S) q) :
    Width q (inputWordCoefficient p*logSize S) := by
  have hn : Maxwell.signedBitLength q.num ≤ inputWordCoefficient p*logSize S := by
    exact_mod_cast h.1.trans (sourceBitBudget_linear p S)
  have hd : Maxwell.unsignedBitLength q.den ≤ inputWordCoefficient p*logSize S := by
    exact_mod_cast h.2.trans (sourceBitBudget_linear p S)
  simp only [Maxwell.signedBitLength,Maxwell.Codec.unsignedBitLength_eq_size,
    ← Nat.size_eq_bits_len] at hn hd
  exact ⟨by omega,hd⟩

private theorem width_abs {q : ℚ} {B : ℕ} (h : Width q B) : Width |q| B := by
  rcases le_total 0 q with hq | hq
  · simpa only [abs_of_nonneg hq] using h
  · simpa only [abs_of_nonpos hq] using h.neg

private theorem magnitude_width (qs : List ℚ) (B : ℕ) (hB : 1≤B)
    (h : ∀q∈qs,Width q B) : Width (Normalization.magnitudeMax qs) B := by
  induction qs with
  | nil =>
    constructor
    · change 0≤B
      omega
    · change 1≤B
      exact hB
  | cons q qs ih =>
    have hq := width_abs (h q (by simp))
    have ht := ih (fun r hr => h r (by simp [hr]))
    rcases le_total |q| (Normalization.magnitudeMax qs) with hle | hle
    · simpa only [Normalization.magnitudeMax,max_eq_right hle] using ht
    · simpa only [Normalization.magnitudeMax,max_eq_left hle] using hq

theorem normalizationScale_width (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 0<S.nnz) (hp : Source.Promises p S) :
    Width (normalizationScale S) (normalizationWordCoefficient p*logSize S) := by
  have hB : 1 ≤ inputWordCoefficient p*logSize S :=
    Nat.mul_pos (by unfold inputWordCoefficient; omega) (Parameters.inputLog_pos S.nnz)
  have ha : Width (Normalization.matrixMax S) (inputWordCoefficient p*logSize S) := by
    apply magnitude_width _ _ hB
    intro q hq
    obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hq
    exact input_width (hp.2.2.1 ij.1 ij.2)
  have hb : Width (Normalization.sourceScale S) (inputWordCoefficient p*logSize S) := by
    apply magnitude_width _ _ hB
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact input_width (hp.2.2.2 i)
  have hsize := Maxwell.Codec.unsignedBitLength_mono (Parameters.input_le_binary S.nnz)
  rw [Maxwell.Dyadic.denominator_bitLength,Maxwell.Codec.unsignedBitLength_eq_size,
    ← Nat.size_eq_bits_len] at hsize
  change S.nnz.bits.length≤logSize S+1 at hsize
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hmW : Width (S.nnz : ℚ) (2*logSize S) := by
    constructor
    · simp only [Rat.num_natCast,Int.natAbs_natCast]
      omega
    · simp only [Rat.den_natCast]
      change 1≤2*logSize S
      omega
  have hscale := hmW.mul ha
  change Width (Normalization.matrixScale S) _ at hscale
  have hout := hb.mul (hscale.inv (Normalization.matrixScale_pos S hm).ne')
  change Width (normalizationScale S) _ at hout
  convert hout using 1
  unfold normalizationWordCoefficient
  ring

theorem normalizationScale_word_bits (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 0<S.nnz) (hp : Source.Promises p S) :
    Maxwell.rationalBitLength (normalizationScale S)≤
      (2*normalizationWordCoefficient p+1)*logSize S := by
  have h := normalizationScale_width p S hm hp
  have hℓ := Parameters.inputLog_pos S.nnz
  simp only [Maxwell.rationalBitLength,Maxwell.signedBitLength,
    Maxwell.Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
  nlinarith only [h.num,h.den,hℓ]

#print axioms normalizationScale_width
#print axioms normalizationScale_word_bits

end Maxwell.Continuum.RealizationParameters
