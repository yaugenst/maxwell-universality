import Maxwell.Continuum.CalibrationCouplingRounded

/-! The actual calibrated operator bounds the finite quadratic value,
so the dyadic coupling interval has no assumed output-range premise. -/

noncomputable section
namespace Maxwell.Continuum.Calibration

open Auxiliary EffectiveMass MasterConstants RationalWords
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem usefulCoupling_quadratic_range {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (q : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ 1)
    (hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤ 1)
    (hq : |(q : ℝ)-(inner ℂ v (B v)).re| ≤ 1) : |(q : ℝ)| ≤ 21*(L : ℝ)^2 := by
  have hv2 : ‖v‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add v (realMode D (inverse_length_le_1024 hL))
    rw [realMode_norm] at ht
    linarith only [ht, hv]
  have hbnorm : ‖B‖ ≤ 4*(L : ℝ)^2+1 := by
    have ht := norm_le_norm_sub_add B
      (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1))
    have hb := physicalWellBlock_coarse_norm D le_rfl (by positivity) d (Pi.single j 1)
    linarith only [ht, hb, hB]
  have hquad : |(inner ℂ v (B v)).re| ≤ 4*(4*(L : ℝ)^2+1) := by
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_inner_le_norm (𝕜 := ℂ) v (B v)).trans
    have hh := mul_le_mul hv2 ((B.le_of_opNorm_le hbnorm v).trans
      (mul_le_mul_of_nonneg_left hv2 (by positivity : (0 : ℝ) ≤ 4*(L : ℝ)^2+1)))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have ht := abs_add_le ((q : ℝ)-(inner ℂ v (B v)).re) (inner ℂ v (B v)).re
  rw [sub_add_cancel] at ht
  have hL1 := length_ge_one hL
  have hsq : (1 : ℝ) ≤ (L : ℝ)^2 := one_le_pow₀ hL1
  linarith only [ht, hq, hquad, hsq]

theorem usefulCoupling_quadratic_binary {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) (ℓ : ℕ)
    (hbinary : (L : ℝ) ≤ (2 : ℝ)^ℓ)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (q : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ 1)
    (hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤ 1)
    (hq : |(q : ℝ)-(inner ℂ v (B v)).re| ≤ 1) : |q| ≤ (2 : ℚ)^(2*ℓ+5) := by
  have hr := usefulCoupling_quadratic_range hL D d j B v q hv hB hq
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg L) hbinary 2
  have hb : 21*(L : ℝ)^2 ≤ (2 : ℝ)^(2*ℓ+5) := by
    rw [pow_add, show 2*ℓ = ℓ*2 by omega, pow_mul]
    norm_num only [show (2 : ℝ)^5 = 32 by norm_num]
    nlinarith only [hs, sq_nonneg ((2 : ℝ)^ℓ)]
  exact_mod_cast hr.trans hb

theorem usefulCoupling_output_width {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) (N ℓ : ℕ)
    (hbinary : (L : ℝ) ≤ (2 : ℝ)^ℓ)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (q : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ (1/2 : ℝ)^(N+2*ℓ+8))
    (hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤
      (1/2 : ℝ)^(N+5))
    (hq : |(q : ℝ)-(inner ℂ v (B v)).re| ≤ (1/2 : ℝ)^(N+6)) :
    Width (roundedCouplingInterval q N).lo (3*N+2*ℓ+17) ∧
    Width (roundedCouplingInterval q N).hi (3*N+2*ℓ+17) := by
  have hb := usefulCoupling_quadratic_binary hL D d j ℓ hbinary B v q
    (hv.trans (pow_le_one₀ (by norm_num) (by norm_num)))
    (hB.trans (pow_le_one₀ (by norm_num) (by norm_num)))
    (hq.trans (pow_le_one₀ (by norm_num) (by norm_num)))
  have hh := roundedCouplingInterval_endpoint_width hb N
  exact ⟨hh.1.mono (by omega), hh.2.mono (by omega)⟩

#print axioms usefulCoupling_quadratic_range
#print axioms usefulCoupling_output_width

end Maxwell.Continuum.Calibration
