import Maxwell.Continuum.CalibrationSupercellFactor
import Maxwell.Continuum.CalibrationFiniteData

/-! Executable physical Fourier coefficients for a stored normalized
supercell vector. Rationalizing the physical normalization has explicit
relative L² error and adds only linearly many coefficient bits. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber RationalWords

def physicalCoefficientData (M P : ℕ) (v : FourierData) : FourierData :=
  FourierData.scale (physicalFactorApprox M P) v

theorem physicalCoefficientData_radius (M P : ℕ) (v : FourierData) :
    (physicalCoefficientData M P v).radius=v.radius := rfl

variable (M : ℕ) [NeZero M]

theorem physicalCoefficientData_real_width (P : ℕ) (v : FourierData) (n : Alias) (j : Fin 3)
    {B : ℕ} (h : Width (v.field n j).1 B) :
    Width ((physicalCoefficientData M P v).field n j).1 (B+6*M.bits.length+P+19) := by
  rw [physicalCoefficientData,FourierData.scale_field]
  change Width (physicalFactorApprox M P*(v.field n j).1) _
  exact ((physicalFactorApprox_width M P).mul h).mono (by omega)

theorem physicalCoefficientData_imag_width (P : ℕ) (v : FourierData) (n : Alias) (j : Fin 3)
    {B : ℕ} (h : Width (v.field n j).2 B) :
    Width ((physicalCoefficientData M P v).field n j).2 (B+6*M.bits.length+P+19) := by
  rw [physicalCoefficientData,FourierData.scale_field]
  change Width (physicalFactorApprox M P*(v.field n j).2) _
  exact ((physicalFactorApprox_width M P).mul h).mono (by omega)

noncomputable section

def physicalSeriesField (v : FourierData) : FieldL2 :=
  (physicalFactor M : ℂ)⁻¹ • embedding M v.value

theorem physicalCoefficientData_series (P : ℕ) (v : FourierData) :
    physicalSeriesField M (physicalCoefficientData M P v)=
      (((physicalFactorApprox M P : ℝ)/physicalFactor M : ℝ) : ℂ) • embedding M v.value := by
  rw [physicalSeriesField,physicalCoefficientData,FourierData.scale_value,map_smul,smul_smul]
  congr 1
  rw [Complex.ofReal_div,Complex.ofReal_ratCast,div_eq_mul_inv,mul_comm]

theorem physicalCoefficientData_error (P : ℕ) (v : FourierData) :
    ‖physicalSeriesField M (physicalCoefficientData M P v)-embedding M v.value‖=
      |(physicalFactorApprox M P : ℝ)/physicalFactor M-1| * ‖v.value‖ := by
  rw [physicalCoefficientData_series]
  have he (c : ℝ) (f : FieldL2) : (c : ℂ) • f-f=((c-1 : ℝ) : ℂ) • f := by
    rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,embedding_norm]

theorem physicalCoefficientData_requested_error (N ell P : ℕ) (v : FourierData)
    (hM : (M : ℝ)≤(2 : ℝ)^ell) (hP : N+3*ell+3≤P) :
    ‖physicalSeriesField M (physicalCoefficientData M P v)-embedding M v.value‖≤
      (1/2 : ℝ)^N*‖v.value‖ := by
  rw [physicalCoefficientData_error]
  exact mul_le_mul_of_nonneg_right
    (physicalFactorApprox_relative_requested M N ell P hM hP) (norm_nonneg v.value)

theorem physicalCoefficientData_mode_error (N ell P : ℕ) (v : FourierData) (f : FieldL2)
    (hM : (M : ℝ)≤(2 : ℝ)^ell) (hP : N+3*ell+5≤P)
    (hv : ‖v.value‖≤2) (he : ‖embedding M v.value-f‖≤(1/2 : ℝ)^(N+1)) :
    ‖physicalSeriesField M (physicalCoefficientData M P v)-f‖≤(1/2 : ℝ)^N := by
  have h1 := physicalCoefficientData_requested_error M (N+2) ell P v hM (by omega)
  have h2 : (1/2 : ℝ)^(N+2)*‖v.value‖≤(1/2 : ℝ)^(N+1) := by
    calc
      _ ≤ (1/2 : ℝ)^(N+2)*2 := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have ht := (norm_sub_le_norm_sub_add_norm_sub
    (physicalSeriesField M (physicalCoefficientData M P v)) (embedding M v.value) f).trans
      (add_le_add (h1.trans h2) he)
  calc
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+1) := ht
    _ = _ := by rw [pow_succ]; ring

#print axioms physicalCoefficientData_requested_error

end
end Maxwell.Continuum.Calibration.Supercell
