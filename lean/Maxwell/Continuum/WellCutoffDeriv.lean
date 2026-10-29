import Maxwell.Continuum.WellCutoff
import Maxwell.Continuum.WellGevrey
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Quantitative derivatives of the literal normalized one-dimensional cutoff. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory Set

def unitVector : Space := PiLp.single 2 (0 : Fin 3) (1 : ℝ)

theorem unitVector_norm : ‖unitVector‖ = 1 := by
  simp [unitVector, PiLp.norm_single]

def lineWell (s : ℝ) : ℝ := w (s • unitVector)

theorem lineWell_contDiff : ContDiff ℝ (⊤ : ℕ∞) lineWell :=
  w_contDiff.comp (by fun_prop)

theorem lineWell_gevrey (K : ℕ) (s : ℝ) :
    |iteratedDeriv K lineWell s| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  have h := w_directional_gevrey (s • unitVector) unitVector unitVector_norm.le K
  rw [directionalDerivative_eq_line K w w_contDiff] at h
  have he : (fun t : ℝ => w (s • unitVector + t • unitVector)) =
      (fun t : ℝ => lineWell (s + t)) := by
    funext t
    unfold lineWell
    rw [add_smul]
  rw [he, iteratedDeriv_comp_const_add] at h
  simpa only [add_zero] using h

theorem cutoffBase_eq_lineWell (s : ℝ) : cutoffBase s = lineWell (2 * s) := by
  rw [lineWell, w_eq_glue, norm_smul, unitVector_norm, mul_one, Real.norm_eq_abs, sq_abs]
  unfold cutoffBase
  congr 1
  ring

theorem cutoffBase_gevrey (K : ℕ) (s : ℝ) :
    |iteratedDeriv K cutoffBase s| ≤ (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  have he : cutoffBase = (fun t : ℝ => lineWell (2 * t)) := funext cutoffBase_eq_lineWell
  rw [he, iteratedDeriv_comp_const_mul (lineWell_contDiff.of_le (by simp)), abs_mul,
    abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    (2 : ℝ) ^ K * |iteratedDeriv K lineWell (2 * s)| ≤
        (2 : ℝ) ^ K * ((400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2) := by
      gcongr
      exact lineWell_gevrey K _
    _ = (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by rw [← mul_assoc, ← mul_pow]; norm_num

theorem psi0_gevrey (K : ℕ) (s : ℝ) :
    |iteratedDeriv K psi0 s| ≤ 8 * (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  change |iteratedDeriv K (fun t => cutoffBase t / cutoffNormalization) s| ≤ _
  rw [iteratedDeriv_div_const, abs_div, abs_of_pos cutoffNormalization_pos]
  apply (div_le_iff₀ cutoffNormalization_pos).mpr
  have h := cutoffBase_gevrey K s
  have hN := cutoffNormalization_bounds.1
  have hC : 0 ≤ (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hN)]

theorem psi_eq_intervalIntegral (s : ℝ) :
    psi s = ∫ t in (s - 3 / 2)..(s + 3 / 2), psi0 t := by
  rw [psi_eq_integral, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    by_cases ht : t ∈ Icc (s - 3 / 2) (s + 3 / 2)
    · have hw : s - t ∈ Icc (-3 / 2 : ℝ) (3 / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simp [cutoffWindow, hw, ht]
    · have hw : s - t ∉ Icc (-3 / 2 : ℝ) (3 / 2) := by
        intro hm
        exact ht ⟨by linarith [hm.2], by linarith [hm.1]⟩
      simp [cutoffWindow, hw, ht])

theorem psi_eq_antiderivative (s : ℝ) :
    psi s = (∫ t in (0 : ℝ)..(s + 3 / 2), psi0 t) - ∫ t in (0 : ℝ)..(s - 3 / 2), psi0 t := by
  rw [psi_eq_intervalIntegral, intervalIntegral.integral_interval_sub_left
    (psi0_contDiff.continuous.intervalIntegrable _ _) (psi0_contDiff.continuous.intervalIntegrable _ _)]

theorem psi_hasDerivAt (s : ℝ) : HasDerivAt psi (psi0 (s + 3 / 2) - psi0 (s - 3 / 2)) s := by
  have h₁ := (psi0_contDiff.continuous.integral_hasStrictDerivAt 0 (s + 3 / 2)).hasDerivAt.comp s
    ((hasDerivAt_id s).add_const (3 / 2))
  have h₂ := (psi0_contDiff.continuous.integral_hasStrictDerivAt 0 (s - 3 / 2)).hasDerivAt.comp s
    ((hasDerivAt_id s).sub_const (3 / 2))
  have he : psi = (fun x => (∫ t in (0 : ℝ)..(x + 3 / 2), psi0 t) -
      ∫ t in (0 : ℝ)..(x - 3 / 2), psi0 t) := funext psi_eq_antiderivative
  rw [he]
  convert! h₁.sub h₂ using 1; simp only [mul_one]

theorem psi_deriv : deriv psi = (fun s => psi0 (s + 3 / 2) - psi0 (s - 3 / 2)) :=
  funext (fun s => (psi_hasDerivAt s).deriv)

theorem psi_iteratedDeriv_succ (K : ℕ) (s : ℝ) :
    iteratedDeriv (K + 1) psi s =
      iteratedDeriv K psi0 (s + 3 / 2) - iteratedDeriv K psi0 (s - 3 / 2) := by
  rw [iteratedDeriv_succ', psi_deriv]
  have h₁ : ContDiff ℝ (K : ℕ) (fun t : ℝ => psi0 (t + 3 / 2)) :=
    (psi0_contDiff.of_le (by simp)).comp (contDiff_id.add contDiff_const)
  have h₂ : ContDiff ℝ (K : ℕ) (fun t : ℝ => psi0 (t - 3 / 2)) :=
    (psi0_contDiff.of_le (by simp)).comp (contDiff_id.sub contDiff_const)
  rw [iteratedDeriv_fun_sub h₁.contDiffAt h₂.contDiffAt,
    iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]

theorem psi_iteratedDeriv_succ_bound (K : ℕ) (s : ℝ) :
    |iteratedDeriv (K + 1) psi s| ≤ 16 * (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  rw [psi_iteratedDeriv_succ]
  have ha := abs_sub (iteratedDeriv K psi0 (s + 3 / 2)) (iteratedDeriv K psi0 (s - 3 / 2))
  linarith [psi0_gevrey K (s + 3 / 2), psi0_gevrey K (s - 3 / 2)]

theorem psi_gevrey (K : ℕ) (s : ℝ) :
    |iteratedDeriv K psi s| ≤ 16 * (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  cases K with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg (psi_nonneg s)]
    linarith [psi_le_one s]
  | succ K =>
    apply (psi_iteratedDeriv_succ_bound K s).trans
    have hf : (K.factorial : ℝ) ≤ ((K + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ K)
    have hp : (800 : ℝ) ^ K ≤ 800 ^ (K + 1) := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
    gcongr

end Maxwell.Continuum.Well
