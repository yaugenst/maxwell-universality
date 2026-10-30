import Maxwell.Continuum.UsefulCoupling

/-! Actual two-well coupling error under finite operator and normalized
mode approximation. No self-adjointness of the offsite block is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open Auxiliary EffectiveMass Bloch CellGauge MasterConstants

theorem physicalWellBlock_coarse_norm {L : ℕ} {z σ : ℝ}
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (d : ℕ) (ν : Bloch.Alias) :
    ‖physicalWellBlock D hσ0 hσ d ν‖ ≤ 4*(L : ℝ)^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [physicalWellBlock_apply]
  calc
    _ ≤ ‖Auxiliary.resolvent D hσ0 hσ
        (fieldTranslation (latticeShift (placementCell L d ν)) (Qh (L : ℝ)⁻¹ f))‖ := by
      simpa only [one_mul] using (Qh (L : ℝ)⁻¹).le_of_opNorm_le (Qh_norm_le (L : ℝ)⁻¹) _
    _ ≤ (4*(L : ℝ)^2)*
        ‖fieldTranslation (latticeShift (placementCell L d ν)) (Qh (L : ℝ)⁻¹ f)‖ :=
      (Auxiliary.resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le_length D hσ0 hσ) _
    _ ≤ (4*(L : ℝ)^2)*‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_mul] using (Qh (L : ℝ)⁻¹).le_of_opNorm_le (Qh_norm_le (L : ℝ)⁻¹) f

theorem quadratic_approximation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) (u v : H) {a e δ : ℝ}
    (hA : ‖A‖ ≤ a) (hu : ‖u‖ = 1) (he : ‖v-u‖ ≤ e) (he1 : e ≤ 1)
    (hδ : ‖B-A‖ ≤ δ) :
    ‖inner ℂ v (B v)-inner ℂ u (A u)‖ ≤ 3*a*e+4*δ := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hA
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hv : ‖v‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add v u
    rw [hu] at ht
    linarith only [ht, he, he1]
  have h1 : ‖inner ℂ (v-u) (A v)‖ ≤ 2*a*e := by
    have hh := (norm_inner_le_norm (𝕜 := ℂ) (v-u) (A v)).trans
      (mul_le_mul he ((A.le_of_opNorm_le hA v).trans
        (mul_le_mul_of_nonneg_left hv ha0)) (norm_nonneg _) he0)
    nlinarith only [hh]
  have h2 : ‖inner ℂ u (A (v-u))‖ ≤ a*e := by
    apply (norm_inner_le_norm (𝕜 := ℂ) u (A (v-u))).trans
    rw [hu, one_mul]
    exact (A.le_of_opNorm_le hA _).trans (mul_le_mul_of_nonneg_left he ha0)
  have h3 : ‖inner ℂ v ((B-A) v)‖ ≤ 4*δ := by
    have hh := (norm_inner_le_norm (𝕜 := ℂ) v ((B-A) v)).trans
      (mul_le_mul hv (((B-A).le_of_opNorm_le hδ v).trans
        (mul_le_mul_of_nonneg_left hv hδ0)) (norm_nonneg _) (by norm_num))
    nlinarith only [hh]
  have hid : inner ℂ v (B v)-inner ℂ u (A u) =
      inner ℂ (v-u) (A v)+inner ℂ u (A (v-u))+inner ℂ v ((B-A) v) := by
    simp only [inner_sub_left, map_sub, inner_sub_right, sub_apply]
    ring
  rw [hid]
  exact norm_add₃_le.trans (by linarith only [h1, h2, h3])

theorem usefulCoupling_approximation {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) {e δ : ℝ}
    (he : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ e) (he1 : e ≤ 1)
    (hδ : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤ δ) :
    |(inner ℂ v (B v)).re-usefulCoupling hL D d j| ≤ 12*(L : ℝ)^2*e+4*δ := by
  have hh := quadratic_approximation _ B (realMode D (inverse_length_le_1024 hL)) v
    (physicalWellBlock_coarse_norm D le_rfl (by positivity) d (Pi.single j 1))
    (realMode_norm D (inverse_length_le_1024 hL)) he he1 hδ
  apply (Complex.abs_re_le_norm
    (inner ℂ v (B v)-inner ℂ (realMode D (inverse_length_le_1024 hL))
      (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)
        (realMode D (inverse_length_le_1024 hL))))).trans
  convert hh using 1
  ring

#print axioms physicalWellBlock_coarse_norm
#print axioms usefulCoupling_approximation

end Maxwell.Continuum.Calibration
