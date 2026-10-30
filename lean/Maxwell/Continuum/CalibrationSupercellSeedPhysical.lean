import Maxwell.Continuum.CalibrationSupercellPointwise
import Maxwell.Continuum.CalibrationSupercellWell
import Maxwell.Continuum.EffectiveMassStartingEnvelope

/-! The finite zero-grid Fourier seed, after actual well multiplication,
is exactly the physical starting envelope with its supercell normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set EffectiveMass

variable (M : ℕ) [NeZero M]

omit [NeZero M] in
theorem physicalFactor_rpow : physicalFactor M=(2*(M : ℝ))^(-(3/2 : ℝ)) := by
  rw [physicalFactor,cellFactor,gridFactor,← mul_inv,← Real.sqrt_mul (by norm_num : (0 : ℝ)≤8)]
  rw [show 8*(M : ℝ)^3=(2*(M : ℝ))^3 by ring,
    Real.sqrt_eq_rpow,← Real.rpow_natCast_mul (by positivity : 0≤2*(M : ℝ)),
    Real.rpow_neg (by positivity : 0≤2*(M : ℝ))]
  norm_num

omit [NeZero M] in
theorem seed_normalization {L : ℝ} (hL : 0<L) :
    (2*(M : ℝ)/L)^(-(3/2 : ℝ))*(L⁻¹)^(3/2 : ℝ)=physicalFactor M := by
  rw [Real.div_rpow (by positivity : 0≤2*(M : ℝ)) hL.le,Real.inv_rpow hL.le,
    Real.rpow_neg hL.le,div_inv_eq_mul,
    mul_inv_cancel_right₀ (Real.rpow_pos_of_pos hL (3/2 : ℝ)).ne',physicalFactor_rpow]

theorem Qh_seed_ae {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ)) (i : Fin 3) :
    Qh L⁻¹ (embedding M (Complex.I • injection M 0 CornerBridge.topState.val)) i =ᵐ[volume]
      fun x => (physicalFactor M : ℂ)*(Well.qw (L⁻¹ • x) : ℂ)*referenceField x i := by
  have he := embedding_injection_zero_ae M CornerBridge.topState.val topState_summable_norm i
  rw [map_smul]
  filter_upwards [Qh_ae L⁻¹ (Complex.I • embedding M (injection M 0 CornerBridge.topState.val)) i,
    Lp.coeFn_smul Complex.I (embedding M (injection M 0 CornerBridge.topState.val) i),he]
      with x hq hi he
  rw [hq]
  simp only [PiLp.smul_apply]
  rw [hi]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [he,referenceField_eq_fourier]
  simp only [PiLp.smul_apply,smul_eq_mul]
  by_cases hx : cellIndex x∈representedCells M
  · rw [ite_eq_left hx]
    ring
  · rw [ite_eq_right hx,mul_zero,mul_zero]
    have hnorm : L≤‖x‖ := by
      by_contra hn
      exact hx (ballCells_subset_represented M hL hM
        (cellIndex_mem_ballCells (le_of_lt (lt_of_not_ge hn))))
    have hz : Well.qw (L⁻¹ • x)=0 := by
      apply (Well.qw_zero_iff _).mpr
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by linarith : 0<L))]
      exact (le_inv_mul_iff₀ (by linarith : 0<L)).mpr (by simpa only [mul_one] using hnorm)
    rw [hz,Complex.ofReal_zero,mul_zero,zero_mul]

theorem physical_seed {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ)) :
    Qh L⁻¹ (embedding M (Complex.I • injection M 0 CornerBridge.topState.val))=
      (((2*(M : ℝ)/L)^(-(3/2 : ℝ)) : ℝ) : ℂ) •
        startingEnvelope (inv_pos.mpr (by linarith : 0<L)) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [Qh_seed_ae M hL hM i,
    startingEnvelope_ae (inv_pos.mpr (by linarith : 0<L)) i,
    Lp.coeFn_smul ((((2*(M : ℝ)/L)^(-(3/2 : ℝ))) : ℝ) : ℂ)
      (startingEnvelope (inv_pos.mpr (by linarith : 0<L)) i)] with x hq he hs
  change _=((((2*(M : ℝ)/L)^(-(3/2 : ℝ)) : ℝ) : ℂ) •
    (startingEnvelope (inv_pos.mpr (by linarith : 0<L)) i)) x
  rw [hq,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [he,Complex.ofReal_mul]
  calc
    _ = ((((2*(M : ℝ)/L)^(-(3/2 : ℝ))*(L⁻¹)^(3/2 : ℝ)) : ℝ) : ℂ)*
        (Well.qw (L⁻¹ • x) : ℂ)*referenceField x i := by
      rw [seed_normalization M (by linarith : 0<L)]
    _ = _ := by rw [Complex.ofReal_mul]; ring

theorem embedding_well_seed (hEven : Even M) {L : ℝ} (hL : 1≤L)
    (hM : 16*(L+1)≤(M : ℝ)) (hs : 4≤2*(M : ℝ)/L) :
    embedding M (aliasMultiplier (rootTorus (2*(M : ℝ)/L) hs)
      (Complex.I • injection M 0 CornerBridge.topState.val))=
      (((2*(M : ℝ)/L)^(-(3/2 : ℝ)) : ℝ) : ℂ) •
        startingEnvelope (inv_pos.mpr (by linarith : 0<L)) := by
  rw [← Qh_embedding M hEven hL hM hs]
  exact physical_seed M hL hM

#print axioms embedding_well_seed

end Maxwell.Continuum.Calibration.Supercell
