import Maxwell.Continuum.CalibrationCompactOutput
import Maxwell.Continuum.CalibrationFiniteAlgorithm

/-! One executable output-template constructor at the actual finite
algorithm's parameters. Its only remaining numerical input theorem is
the finite mode accuracy supplied by calibration. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open Supercell Profile EffectiveMass FiniteAuxiliary MeasureTheory

def outputSupportBits (L r N : ℕ) (z : ℚ) : ℕ :=
  lengthBits (2*(mode L r (N+2) z).radius+1)

def outputTemplateBits (L r N : ℕ) (z : ℚ) : List Bool :=
  compactOutputBits (size L r (N+2)) (L : ℚ) (mode L r (N+2) z) N
    (lengthBits (size L r (N+2))) (outputSupportBits L r N z) (lengthBits L)

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] size precision mode realMode

def outputTemplateField (L r N : ℕ) (z : ℚ) (hL : 0<L) (center : Space) : FieldL2 :=
  compactTemplateField (size L r (N+2)) (L : ℚ) (mode L r (N+2) z) N
    (lengthBits (size L r (N+2))) (outputSupportBits L r N z) (lengthBits L)
    (by exact_mod_cast hL) center

theorem outputTemplate_certificate {L : ℕ} (hL : 0<L) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹≤1/(2 : ℝ)^1024)
    (he : ‖embedding (size L r (N+2)) (mode L r (N+2) z).value-realMode D hh‖≤(1/2 : ℝ)^(N+2))
    (center : Space) :
    fieldConjugation (outputTemplateField L r N z hL center)=outputTemplateField L r N z hL center ∧
      ‖outputTemplateField L r N z hL center‖≤2 ∧
      (∀i,∀ᵐx∂(volume : Measure Space),x∉Metric.ball center (L : ℝ) →
        outputTemplateField L r N z hL center i x=0) ∧
      ‖outputTemplateField L r N z hL center-siteInsertion (L : ℝ)⁻¹ center (realMode D hh)‖≤
        (1/2 : ℝ)^N := by
  have hLr : (1 : ℝ)≤L := by exact_mod_cast hL
  have hv : ‖(mode L r (N+2) z).value‖≤2 := by
    have ht := norm_le_norm_sub_add (embedding (size L r (N+2)) (mode L r (N+2) z).value) (realMode D hh)
    rw [embedding_norm,realMode_norm] at ht
    have hp : (1/2 : ℝ)^(N+2)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith only [ht,he,hp]
  have hgeometry : 16*((L : ℝ)+1)≤(size L r (N+2) : ℝ) := by
    have h := size_geometry L r (N+2)
    have hr : (0 : ℝ)≤r := Nat.cast_nonneg r
    linarith only [h,hr]
  have hc := compactTemplate_certificate (size L r (N+2)) (size_even L r (N+2)) (L : ℚ)
    (by simpa only [Rat.cast_natCast] using hLr)
    (by simpa only [Rat.cast_natCast] using hgeometry)
    (mode L r (N+2) z) N (lengthBits (size L r (N+2)))
    (outputSupportBits L r N z) (lengthBits L) hv
    (lengthBits_bound (size L r (N+2))) (lengthBits_bound (2*(mode L r (N+2) z).radius+1))
    (by simpa only [Rat.cast_natCast] using lengthBits_bound L) D hh he center
  exact hc

#print axioms outputTemplate_certificate

end
end Maxwell.Continuum.Calibration.FiniteAlgorithm
