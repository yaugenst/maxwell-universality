import Maxwell.Composition.SelectedCoefficientWidths
import Maxwell.Composition.SelectedScaleWidth

/-! All stored decoder weights and every finite message output have
logarithmic reduced width, independently of the random good event. -/
noncomputable section
namespace Maxwell.Composition.SelectedDecoderWidths
open Maxwell.Realization Maxwell.Composition.SelectedWidths
open Maxwell.Composition.SelectedCoefficientWidths Maxwell.Composition.SelectedScaleWidth
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def weightCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  1+scaleCoefficient p+incrementCoefficient p R+coordinateCoefficient p R
def outputCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  weightCoefficient p R+localCount R*(weightCoefficient p R+formatCoefficient p R+2)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm
local notation "B" => unsignedBitLength (2+S.nnz)

theorem weight_short (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S)
    (J : ℕ) (j : Fin J) (i : Fin S.n) (k : Fin ((I).target R J j).decoder.sampleCount) :
    Source.ShortRational ((weightCoefficient p R*B:ℕ):ℝ)
      (((I).target R J j).decoder.weight i k) := by
  have hs := scale_short p S hp hm
  have hv := increments_short p S hm R hm2 hp.1 (SourcePhysicalDecoder.vertex S (I).precision i)
  have hq := coordinates_short p S hm R hm2 hp.1 (finProdFinEquiv.symm k).2
  have h := hs.mul (hv.mul hq)
  change Source.ShortRational _ (((I).target R J j).decoder.weight i k) at h
  apply h.mono
  unfold weightCoefficient
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) B]

theorem offset_short (J : ℕ) (j : Fin J) (i : Fin S.n) :
    Source.ShortRational ((weightCoefficient p R*B:ℕ):ℝ)
      (((I).target R J j).decoder.offset i) := by
  change Source.ShortRational _ ((Maxwell.Logical.Normalization.sourceScale S/
    Maxwell.Logical.Normalization.matrixScale S)*0)
  rw [mul_zero]
  apply Source.ShortRational.zero.mono
  have hb := inputBitLength_pos S.nnz
  exact_mod_cast (show 1≤weightCoefficient p R*B by unfold weightCoefficient; nlinarith)

theorem support_card (J : ℕ) (j : Fin J) (i : Fin S.n) :
    ((((I).target R J j).decoder.support i).card) = localCount R :=
  SourcePhysicalDecoder.support_card _ _ _ _ _ _ _ _ _ _ _ _

theorem output_short (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S)
    (J : ℕ) (j : Fin J) (w : ((I).target R J j).decoder.Messages) (i : Fin S.n) :
    Source.ShortRational ((outputCoefficient p R*B:ℕ):ℝ)
      (((I).target R J j).decoder.decode w i) := by
  have h := Maxwell.Codec.decoder_value_short (((I).target R J j).decoder) w i
    (offset_short p S hm R J j i) (fun k _ => weight_short p S hm R hm2 hp J j i k)
  rw [support_card p S hm R J j i] at h
  apply h.mono
  have hf := format_width p S hm R hm2 hp.1
  have hb := inputBitLength_pos S.nnz
  have hformat : (((I).target R J j).decoder.format.width) = ((I).format R).width := rfl
  rw [hformat]
  exact_mod_cast (show weightCoefficient p R*B+localCount R*
      (weightCoefficient p R*B+((I).format R).width+2) ≤ outputCoefficient p R*B by
    unfold outputCoefficient
    nlinarith [Nat.mul_le_mul_left (localCount R) hf,
      Nat.mul_le_mul_left (2*localCount R) hb])

end Maxwell.Composition.SelectedDecoderWidths
