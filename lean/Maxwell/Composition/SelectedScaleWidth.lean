import Maxwell.Codec.RationalShort
import Maxwell.Cost.NormalizeRatio.SourceData
import Maxwell.Cost.MagnitudeMax.SourceSemantics
import Maxwell.Realization.Widths

/-! The exact original-source normalization scale used by the stored
decoder has logarithmic width under the actual input promise. -/
noncomputable section
namespace Maxwell.Composition.SelectedScaleWidth
open Maxwell.Realization Maxwell.Cost Maxwell.Codec
open Maxwell.Logical.Normalization
set_option maxHeartbeats 800000

def inputCoefficient (p : Source.Parameters) : ℕ := 2+Nat.ceil p.inputBitFactor
def scaleCoefficient (p : Source.Parameters) : ℕ := 2+2*inputCoefficient p

theorem log_le_inputBits (m : ℕ) :
    Real.log (2+(m:ℝ)) ≤ (unsignedBitLength (2+m):ℝ) := by
  have hm : (2+(m:ℝ)) ≤ (2:ℝ)^unsignedBitLength (2+m) := by
    exact_mod_cast (show 2+m ≤ 2^unsignedBitLength (2+m) by
      rw [unsignedBitLength_eq_size]
      exact (Nat.lt_size_self _).le)
  have h := Real.log_le_log (by positivity : (0:ℝ)<2+m) hm
  rw [Real.log_pow] at h
  have h2 : Real.log (2:ℝ) ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  exact h.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) (unsignedBitLength (2+m))])

theorem input_width (p : Source.Parameters) (S : Source.SparseSystem) :
    MagnitudeMax.inputWidth p S ≤ inputCoefficient p*unsignedBitLength (2+S.nnz) := by
  have hc : Nat.ceil (Source.bitBudget p S) ≤
      Nat.ceil p.inputBitFactor*unsignedBitLength (2+S.nnz) := by
    apply Nat.ceil_le.mpr
    unfold Source.bitBudget
    have hb := log_le_inputBits S.nnz
    have hp := Nat.le_ceil p.inputBitFactor
    push_cast
    exact (mul_le_mul_of_nonneg_left hb p.inputBitFactor_pos.le).trans
      (mul_le_mul_of_nonneg_right hp (by positivity))
  have hm := unsignedBitLength_mono (show S.nnz≤2+S.nnz by omega)
  have hb := inputBitLength_pos S.nnz
  unfold MagnitudeMax.inputWidth inputCoefficient
  nlinarith

theorem scale_short_raw (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 0 < S.nnz) :
    Source.ShortRational ((S.nnz.size+2*MagnitudeMax.inputWidth p S+1:ℕ):ℝ)
      (sourceScale S/matrixScale S) := by
  let A := NormalizeRatio.matrixScalePair S
  let B := NormalizeRatio.sourceScalePair S
  have hA := NormalizeRatio.matrixScalePair_positive S hm
  have hB : 0 < B.2 := NormalizeRatio.maximum_denominator_pos _
  have hwidth := MagnitudeMax.promised_entry_width p S hp
  have hvalues : ∀ q ∈ matrixValues S,
      q.num.natAbs.bits.length ≤ MagnitudeMax.inputWidth p S ∧
      q.den.bits.length ≤ MagnitudeMax.inputWidth p S := by
    intro q hq
    rw [← MagnitudeMax.source_values S] at hq
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
    exact (hwidth entry he).2.2
  have ha := NormalizeRatio.matrixScalePair_bits S (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth_pos p S) (fun q hq => (hvalues q hq).1)
    (fun q hq => (hvalues q hq).2)
  have hb := MagnitudeMax.maximum_width (List.ofFn S.source)
    (MagnitudeMax.inputWidth p S) (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth_pos p S)
    (fun q hq => (MagnitudeMax.promised_rhs_width p S hp q hq).1)
    (fun q hq => (MagnitudeMax.promised_rhs_width p S hp q hq).2)
  let pair : RationalPair := ⟨(B.1*A.2:ℕ), B.2*A.1, Nat.mul_pos hB hA.1⟩
  have hvalue : pair.value = sourceScale S/matrixScale S := by
    rw [←NormalizeRatio.sourceScalePair_value S,←NormalizeRatio.matrixScalePair_value S]
    dsimp [pair,RationalPair.value,A,B]
    push_cast
    field_simp
  rw [←hvalue]
  apply RationalPair.value_short
  have hn := unsignedBitLength_mul_le B.1 A.2
  have hd := unsignedBitLength_mul_le B.2 A.1
  change A.1.bits.length ≤ S.nnz.bits.length+MagnitudeMax.inputWidth p S ∧
    A.2.bits.length≤MagnitudeMax.inputWidth p S at ha
  change B.1.bits.length≤MagnitudeMax.inputWidth p S ∧
    B.2.bits.length≤MagnitudeMax.inputWidth p S at hb
  simp only [unsignedBitLength_eq_size] at hn hd
  simp only [Nat.size_eq_bits_len] at ha hb
  constructor
  · change signedBitLength (↑(B.1*A.2):ℤ)≤_
    simp only [signedBitLength,Int.natAbs_natCast,unsignedBitLength_eq_size]
    omega
  · change unsignedBitLength (B.2*A.1)≤_
    simp only [unsignedBitLength_eq_size]
    omega

theorem scale_short (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 0 < S.nnz) :
    Source.ShortRational ((scaleCoefficient p*unsignedBitLength (2+S.nnz):ℕ):ℝ)
      (sourceScale S/matrixScale S) := by
  apply (scale_short_raw p S hp hm).mono
  have hi := input_width p S
  have hb := inputBitLength_pos S.nnz
  have hm' := unsignedBitLength_mono (show S.nnz≤2+S.nnz by omega)
  rw [unsignedBitLength_eq_size S.nnz] at hm'
  exact_mod_cast (show S.nnz.size+2*MagnitudeMax.inputWidth p S+1 ≤
      scaleCoefficient p*unsignedBitLength (2+S.nnz) by
    unfold scaleCoefficient
    nlinarith)

end Maxwell.Composition.SelectedScaleWidth
