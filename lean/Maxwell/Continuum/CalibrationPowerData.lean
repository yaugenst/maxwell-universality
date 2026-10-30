import Maxwell.Continuum.CalibrationPowerNormalize
import Maxwell.Continuum.EffectiveMassTheorem

/-! The paper's actual scaled auxiliary operator satisfies the power
iteration hypotheses, with explicit eigenvalue and ratio constants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open TopEigenPerturbation EffectiveMass InnerProductSpace MeasureTheory

attribute [local irreducible] Sh muH realMode Bloch.unitary Auxiliary.resolvent
  scaledEigenvalue startingEnvelope startingVector

def powerScale (h : ℝ) : ℝ := (2 : ℝ)^90*h^2

def powerOperator {h z : ℝ} (D : Auxiliary.Calibration h z) : FieldL2 →L[ℂ] FieldL2 :=
  (powerScale h : ℂ) • Sh D

def powerValue {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : ℝ := powerScale h*muH D hh

theorem powerScale_pos {h : ℝ} (hh : 0 < h) : 0 < powerScale h := by
  exact mul_pos (by positivity) (sq_pos_of_pos hh)

theorem powerData {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    Data (powerOperator D) (realMode D hh) (powerValue D hh) (1/(2 : ℝ)^100) := by
  have hd := (realModeData D hh).positive_scale (powerScale_pos D.h_pos)
  have he : powerScale h*((h^2)⁻¹*(Well.gap/4)) = 1/(2 : ℝ)^100 := by
    rw [powerScale, Well.gap_exact]
    field_simp [D.h_pos.ne']
    ring
  rw [he] at hd
  exact hd

theorem powerValue_eq {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    powerValue D hh = (2 : ℝ)^90*scaledEigenvalue D hh := by
  rw [powerValue, powerScale, muH]
  field_simp [D.h_pos.ne']

theorem powerValue_bounds {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    1/(2 : ℝ)^38 ≤ powerValue D hh ∧ powerValue D hh ≤ 1/2 := by
  rw [powerValue_eq]
  have hb := scaledEigenvalue_bounds D hh
  constructor
  · exact le_trans (by norm_num) (mul_le_mul_of_nonneg_left hb.1 (by positivity))
  · exact (mul_le_mul_of_nonneg_left hb.2 (by positivity)).trans (by norm_num)

theorem powerOperator_norm {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : ‖powerOperator D‖ ≤ 1 := by
  have hd := powerData D hh
  have hm : 0 < powerValue D hh := lt_of_lt_of_le hd.gap_pos hd.gap_le_mu
  have ht := norm_le_norm_sub_add (powerOperator D)
    ((powerValue D hh : ℂ) • rankOne ℂ (realMode D hh) (realMode D hh))
  have hr : ‖(powerValue D hh : ℂ) • rankOne ℂ (realMode D hh) (realMode D hh)‖ = powerValue D hh := by
    rw [norm_smul, norm_rankOne, realMode_norm, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  rw [hr] at ht
  have hc := hd.deflated_norm
  have hb := (powerValue_bounds D hh).2
  linarith

theorem power_ratio {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    powerValue D hh-1/(2 : ℝ)^100 ≤ powerValue D hh*(1-1/(2 : ℝ)^104) := by
  have hb := (powerValue_bounds D hh).2
  have hc : (1/(2 : ℝ)^104)* (1/2) ≤ 1/(2 : ℝ)^100 := by norm_num
  nlinarith

theorem startingEnvelope_real {h : ℝ} (hh : 0 < h) :
    fieldConjugation (startingEnvelope hh) = startingEnvelope hh := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [scalarConjugation_ae (startingEnvelope hh j), startingEnvelope_ae hh j]
    with x hc he
  change scalarConjugation (startingEnvelope hh j) x = startingEnvelope hh j x
  rw [hc,he,star_mul',Complex.star_def,Complex.conj_ofReal]
  have hr := congrArg (fun v : FreeFiber.Polarization => v j) (CellBandFourier.referenceField_real x)
  change star (CellBandFourier.referenceField x j) = CellBandFourier.referenceField x j at hr
  rw [← Complex.star_def,hr]

theorem startingVector_real {h : ℝ} (hh : 0 < h) :
    fieldConjugation (startingVector hh) = startingVector hh := by
  rw [startingVector, NormedSpace.normalize, map_smul, startingEnvelope_real]

def startingCoefficient {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : ℝ :=
  (inner ℂ (realMode D hh) (startingVector D.h_pos)).re

theorem startingCoefficient_inner {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    inner ℂ (realMode D hh) (startingVector D.h_pos) = (startingCoefficient D hh : ℂ) := by
  apply Complex.ext
  · rfl
  · exact inner_im_zero_of_real (realMode_real D hh) (startingVector_real D.h_pos)

theorem startingCoefficient_lower {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : 1/(2 : ℝ)^48 ≤ startingCoefficient D hh := by
  have hs := realMode_starting_overlap D hh
  have he := congrArg Complex.re (inner_conj_symm (𝕜 := ℂ)
    (realMode D hh) (startingVector D.h_pos))
  simp only [Complex.conj_re] at he
  exact hs.trans_eq he

#print axioms powerData
#print axioms powerOperator_norm
#print axioms power_ratio
#print axioms startingCoefficient_lower

end Maxwell.Continuum.Calibration
