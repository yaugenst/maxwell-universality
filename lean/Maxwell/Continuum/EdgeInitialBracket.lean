import Maxwell.Continuum.NaturalSquareRootEvaluation
import Maxwell.Continuum.CalibrationPi
import Maxwell.Continuum.PeriodicPhysicalHessian
import Maxwell.Continuum.EdgeBisection

/-! The literal finite rational initial bracket for the actual continuum edge. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate FreeFiber PeriodicBand

def edgeRho : ℚ := ((2 : ℚ)^100)⁻¹
def edgeReference : ℚ :=
  3*(Elementary.piApprox 256).center^2/4-7+edgeRho*(5+2*sqrtNaturalCenter 19 256)/6
def edgeInitial : Interval :=
  ⟨edgeReference-2^17*edgeRho^2,edgeReference+2^17*edgeRho^2,by
    have h : (0 : ℚ)≤2^17*edgeRho^2 := by positivity
    linarith⟩

attribute [local irreducible] Elementary.piApprox sqrtNaturalCenter edgeReference edgeRho

theorem edgeRho_cast : (edgeRho : ℝ)=backgroundAmplitude := by
  simp only [edgeRho,backgroundAmplitude,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]

theorem edgeReference_error :
    |freeEdge+backgroundAmplitude*Corner.lambdaStar-(edgeReference : ℝ)|≤
      (2 : ℝ)^15*backgroundAmplitude^2 := by
  let p : ℝ := ((Elementary.piApprox 256).center : ℝ)
  let s : ℝ := (sqrtNaturalCenter 19 256 : ℝ)
  let δ : ℝ := (1/2 : ℝ)^256
  have hπ : |Real.pi-p|≤δ := by
    have h := Elementary.piApprox_contains 256
    change |Real.pi-p|≤((Elementary.piApprox 256).radius : ℝ) at h
    rw [Elementary.piApprox_radius] at h
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hδ : δ≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : |p|≤5 := by
    have ht := abs_sub_le p Real.pi 0
    simp only [sub_zero,abs_sub_comm p Real.pi,abs_of_pos Real.pi_pos] at ht
    linarith [Real.pi_lt_four]
  have hsum : |Real.pi+p|≤9 := by
    exact (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_of_pos Real.pi_pos] using Real.pi_lt_four.le) hp).trans_eq (by norm_num))
  have hs : |Real.sqrt 19-s|≤δ := by
    have h := sqrtNaturalApprox_contains 19 256
    change |Real.sqrt 19-s|≤(((1/2 : ℚ)^256 : ℚ) : ℝ) at h
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hLam : |Corner.lambdaStar-(5+2*s)/6|≤δ := by
    rw [Corner.lambdaStar]
    have he : (5+2*Real.sqrt 19)/6-(5+2*s)/6=(Real.sqrt 19-s)/3 := by ring
    rw [he,abs_div,show |(3 : ℝ)|=3 by norm_num]
    exact (div_le_div_of_nonneg_right hs (by norm_num)).trans
      (div_le_self (by positivity) (by norm_num))
  have hfree : |freeEdge-(3*p^2/4-7)|≤7*δ := by
    have he : freeEdge-(3*p^2/4-7)=(3/4 : ℝ)*(Real.pi-p)*(Real.pi+p) := by unfold freeEdge; ring
    rw [he,abs_mul,abs_mul,show |(3/4 : ℝ)|=3/4 by norm_num]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hπ (show (0 : ℝ)≤3/4 by norm_num)) hsum
      (abs_nonneg _) (by positivity)
    nlinarith only [h,show 0≤δ by positivity]
  have hρ : backgroundAmplitude≤1 := backgroundAmplitude_le.trans (by norm_num)
  have he : freeEdge+backgroundAmplitude*Corner.lambdaStar-(edgeReference : ℝ)=
      (freeEdge-(3*p^2/4-7))+backgroundAmplitude*(Corner.lambdaStar-(5+2*s)/6) := by
    simp only [edgeReference,Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
      Rat.cast_ofNat,edgeRho_cast]
    change freeEdge+backgroundAmplitude*Corner.lambdaStar-
      (3*p^2/4-7+backgroundAmplitude*(5+2*s)/6)=_
    ring
  rw [he]
  calc
    _ ≤ |freeEdge-(3*p^2/4-7)|+|backgroundAmplitude*(Corner.lambdaStar-(5+2*s)/6)| := abs_add_le _ _
    _ ≤ 7*δ+1*δ := add_le_add hfree (by
      rw [abs_mul,abs_of_pos backgroundAmplitude_pos]
      exact mul_le_mul hρ hLam (abs_nonneg _) zero_le_one)
    _ ≤ _ := by norm_num [δ,backgroundAmplitude]

theorem edgeInitial_contains : edgeInitial.Contains (dielectricBand 0).re := by
  have hc := (Complex.abs_re_le_norm (dielectricBand 0-
    ((freeEdge : ℂ)+(backgroundAmplitude : ℂ)*(Corner.lambdaStar : ℂ)))).trans center_energy_bound
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hc
  have href := edgeReference_error
  have he := (abs_sub_le (dielectricBand 0).re
    (freeEdge+backgroundAmplitude*Corner.lambdaStar) (edgeReference : ℝ)).trans (add_le_add hc href)
  obtain ⟨hl,hu⟩ := abs_le.mp he
  constructor
  · change ((edgeReference-2^17*edgeRho^2 : ℚ) : ℝ)≤_
    push_cast
    rw [edgeRho_cast]
    nlinarith only [hl,sq_nonneg backgroundAmplitude]
  · change _≤((edgeReference+2^17*edgeRho^2 : ℚ) : ℝ)
    push_cast
    rw [edgeRho_cast]
    nlinarith only [hu,sq_nonneg backgroundAmplitude]

theorem edgeInitial_width : edgeInitial.width=(1/2 : ℚ)^182 := by
  calc
    _ = (2 : ℚ)^18*edgeRho^2 := by unfold edgeInitial Interval.width; ring
    _ = _ := by norm_num [edgeRho]

theorem edgeInitial_width_pos : 0<edgeInitial.width := by rw [edgeInitial_width]; positivity

theorem edgeInitial_scaled_error (q : ℚ) (hq : edgeInitial.lo≤q ∧ q≤edgeInitial.hi) :
    |((q : ℝ)-freeEdge)/backgroundAmplitude-Corner.lambdaStar|≤1/100 := by
  have hq' : |(q : ℝ)-(edgeReference : ℝ)|≤(2 : ℝ)^17*backgroundAmplitude^2 := by
    have hl := (Rat.cast_le (K := ℝ)).mpr hq.1
    have hu := (Rat.cast_le (K := ℝ)).mpr hq.2
    simp only [edgeInitial,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
      edgeRho_cast] at hl hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have href : |(edgeReference : ℝ)-(freeEdge+backgroundAmplitude*Corner.lambdaStar)|≤
      (2 : ℝ)^15*backgroundAmplitude^2 := by simpa only [abs_sub_comm] using edgeReference_error
  have h := (abs_sub_le (q : ℝ) (edgeReference : ℝ)
    (freeEdge+backgroundAmplitude*Corner.lambdaStar)).trans (add_le_add hq' href)
  have he : ((q : ℝ)-freeEdge)/backgroundAmplitude-Corner.lambdaStar=
      ((q : ℝ)-(freeEdge+backgroundAmplitude*Corner.lambdaStar))/backgroundAmplitude := by
    field_simp [backgroundAmplitude_pos.ne']
    ring
  rw [he,abs_div,abs_of_pos backgroundAmplitude_pos]
  apply (div_le_iff₀ backgroundAmplitude_pos).mpr
  apply h.trans
  norm_num [backgroundAmplitude]

#print axioms edgeInitial_contains
#print axioms edgeInitial_scaled_error

end Maxwell.Continuum.Calibration
