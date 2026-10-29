import Maxwell.Continuum.PeriodicImaginaryMonotonicity

/-! Existence, uniqueness and the one-percent enclosure of the actual
small positive imaginary pole of the selected dielectric band. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.PeriodicBand

open Auxiliary FreeFiber Set Metric

attribute [local irreducible] coordinateBand dielectricBand imaginaryRise hessian centerEnergy

def poleLower (h : ℝ) (j : Fin 3) : ℝ := (99 / 100 : ℝ) * h / Real.sqrt (hessian j j)

def poleUpper (h : ℝ) (j : Fin 3) : ℝ := (101 / 100 : ℝ) * h / Real.sqrt (hessian j j)

theorem pole_endpoint_square (h c : ℝ) (j : Fin 3) :
    hessian j j * (c * h / Real.sqrt (hessian j j))^2 = c^2 * h^2 := by
  rw [div_pow, Real.sq_sqrt (hessian_diagonal_positive j).le]
  field_simp [(hessian_diagonal_positive j).ne']

theorem pole_endpoints {h : ℝ} (h0 : 0 < h) (j : Fin 3) :
    0 < poleLower h j ∧ poleLower h j ≤ poleUpper h j ∧ poleUpper h j ≤ 2 * h := by
  have hs := sqrt_hessian_diagonal_ge_one j
  have hsp := Real.sqrt_pos.mpr (hessian_diagonal_positive j)
  constructor
  · exact div_pos (mul_pos (by norm_num) h0) hsp
  constructor
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (99 / 100 : ℝ) ≤ 101 / 100) h0.le) hsp.le
  · change (101 / 100 : ℝ) * h / Real.sqrt (hessian j j) ≤ 2 * h
    exact (div_le_self (mul_nonneg (by norm_num) h0.le) hs).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (101 / 100 : ℝ) ≤ 2) h0.le)

theorem pole_endpoint_values {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    imaginaryRise j (poleLower h j) < centerEnergy - z ∧
      centerEnergy - z < imaginaryRise j (poleUpper h j) := by
  obtain ⟨ha, hab, hb⟩ := pole_endpoints D.h_pos j
  have hla := imaginaryRise_small_error D.h_pos.le hh j ⟨ha.le, hab.trans hb⟩
  have hlb := imaginaryRise_small_error D.h_pos.le hh j ⟨ha.le.trans hab, hb⟩
  have hqa : hessian j j * (poleLower h j)^2 = (99 / 100 : ℝ)^2 * h^2 :=
    pole_endpoint_square h (99 / 100) j
  have hqb : hessian j j * (poleUpper h j)^2 = (101 / 100 : ℝ)^2 * h^2 :=
    pole_endpoint_square h (101 / 100) j
  rw [hqa] at hla
  rw [hqb] at hlb
  have he := abs_le.mp D.error
  have hs := (imaginary_scale_bounds D.h_pos.le hh).2.2.2
  have h4 : h^4 ≤ h^2 / 1000 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg h)]
  have hp := sq_pos_of_pos D.h_pos
  constructor <;> nlinarith [abs_le.mp hla, abs_le.mp hlb]

theorem exists_imaginaryPole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ∃ β ∈ Icc (poleLower h j) (poleUpper h j),
      coordinateBand j ((β : ℂ) * Complex.I) = (z : ℂ) := by
  obtain ⟨ha, hab, hb⟩ := pole_endpoints D.h_pos j
  have hc : ContinuousOn (imaginaryRise j) (Icc (poleLower h j) (poleUpper h j)) := by
    intro β hβ
    apply (imaginaryRise_hasDerivAt j ?_).continuousAt.continuousWithinAt
    rw [abs_of_nonneg (ha.le.trans hβ.1)]
    exact (hβ.2.trans hb).trans_lt
      (lt_of_le_of_lt (imaginary_scale_bounds D.h_pos.le hh).1
        (by linarith [analyticRadius_pos]))
  have hv := pole_endpoint_values D hh j
  obtain ⟨β, hβ, he⟩ := intermediate_value_Icc hab hc ⟨hv.1.le, hv.2.le⟩
  refine ⟨β, hβ, ?_⟩
  apply Complex.ext
  · change (coordinateBand j ((β : ℂ) * Complex.I)).re = z
    unfold imaginaryRise at he
    linarith
  · rw [Complex.ofReal_im]
    apply coordinateBand_imaginary_real j
    rw [abs_of_nonneg (ha.le.trans hβ.1)]
    exact (hβ.2.trans hb).trans_lt
      (lt_of_le_of_lt (imaginary_scale_bounds D.h_pos.le hh).1
        (by linarith [analyticRadius_pos]))

def imaginaryPole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ℝ :=
  (exists_imaginaryPole D hh j).choose

theorem imaginaryPole_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    (99 / 100 : ℝ) * h / Real.sqrt (hessian j j) ≤ imaginaryPole D hh j ∧
      imaginaryPole D hh j ≤ (101 / 100 : ℝ) * h / Real.sqrt (hessian j j) :=
  (exists_imaginaryPole D hh j).choose_spec.1

theorem imaginaryPole_equation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    dielectricBand (((imaginaryPole D hh j : ℂ) * Complex.I) • basisVector j) = (z : ℂ) := by
  simpa only [coordinateBand, imaginaryPole] using (exists_imaginaryPole D hh j).choose_spec.2

theorem imaginaryPole_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : 0 < imaginaryPole D hh j :=
  (pole_endpoints D.h_pos j).1.trans_le (imaginaryPole_bounds D hh j).1

theorem imaginaryPole_mem_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : imaginaryPole D hh j ∈ Icc 0 (2 * h) :=
  ⟨(imaginaryPole_pos D hh j).le,
    (imaginaryPole_bounds D hh j).2.trans (pole_endpoints D.h_pos j).2.2⟩

theorem imaginaryPole_unique {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {β : ℝ}
    (hβ : β ∈ Icc 0 (2 * h))
    (he : dielectricBand (((β : ℂ) * Complex.I) • basisVector j) = (z : ℂ)) :
    β = imaginaryPole D hh j := by
  apply (imaginaryRise_strictMonoOn D.h_pos hh j).injOn hβ (imaginaryPole_mem_small D hh j)
  unfold imaginaryRise coordinateBand
  rw [he, imaginaryPole_equation D hh j]

theorem imaginaryPole_unique_chart {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {β : ℝ}
    (hβ : β ∈ Icc 0 smallRadius)
    (he : dielectricBand (((β : ℂ) * Complex.I) • basisVector j) = (z : ℂ)) :
    β = imaginaryPole D hh j := by
  have hp := imaginaryPole_mem_small D hh j
  have hp' : imaginaryPole D hh j ∈ Icc 0 smallRadius :=
    ⟨hp.1, hp.2.trans (twice_inverse_scale_le_smallRadius hh)⟩
  apply (imaginaryRise_strictMonoOn_chart j).injOn hβ hp'
  unfold imaginaryRise coordinateBand
  rw [he, imaginaryPole_equation D hh j]

end Maxwell.Continuum.PeriodicBand
