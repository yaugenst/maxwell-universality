import Maxwell.Continuum.WeakCurl
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith

/-! The normalized spatial dilation on actual Hilbert-valued L² in
three dimensions, including its inverse and its precise representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.L2Dilation

open MeasureTheory
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev L2 := Lp H 2 (volume : Measure Space)

theorem norm_sq (f : L2 (H := H)) : ‖f‖^2 = ∫ x, ‖f x‖^2 := by
  have he := L2.inner_def (𝕜 := ℂ) f f
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at he
  rw [integral_ofReal] at he
  exact Complex.ofReal_injective he

def factor (a : ℝ) : ℝ := (Real.sqrt (a^3))⁻¹

theorem factor_pos {a : ℝ} (ha : 0 < a) : 0 < factor a := by
  unfold factor
  positivity

theorem factor_square {a : ℝ} (ha : 0 < a) : factor a ^ 2 * a^3 = 1 := by
  rw [factor, inv_pow, Real.sq_sqrt (pow_pos ha _).le, inv_mul_cancel₀ (pow_ne_zero _ ha.ne')]

theorem factor_inverse {a : ℝ} (ha : 0 < a) : factor a⁻¹ * factor a = 1 := by
  rw [factor, factor, inv_pow, Real.sqrt_inv, inv_inv,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (pow_pos ha _)).ne']

theorem inverse_measurePreserving {a : ℝ} (ha : 0 < a) :
    MeasurePreserving (fun x : Space => a⁻¹ • x) volume
      (ENNReal.ofReal (a^3) • volume) where
  measurable := measurable_const_smul a⁻¹
  map_eq := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero ha.ne')]
    simp only [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin,
      inv_pow, inv_inv, abs_of_pos (pow_pos ha 3)]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem inverse_ae {a : ℝ} (ha : 0 < a) {f g : Space → H} (hfg : f =ᵐ[volume] g) :
    (fun x => f (a⁻¹ • x)) =ᵐ[volume] fun x => g (a⁻¹ • x) :=
  (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero ha.ne')).ae_eq_comp hfg

theorem action_memLp {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) :
    MemLp (fun x => (factor a : ℂ) • f (a⁻¹ • x)) 2 (volume : Measure Space) :=
  (((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving
    (inverse_measurePreserving ha)).const_smul _

def action {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) : L2 (H := H) :=
  (action_memLp ha f).toLp _

theorem action_ae {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) :
    action ha f =ᵐ[volume] fun x => (factor a : ℂ) • f (a⁻¹ • x) := MemLp.coeFn_toLp _

theorem action_norm_sq {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) :
    ‖action ha f‖^2 = ‖f‖^2 := by
  rw [norm_sq]
  have he : (fun x => ‖action ha f x‖^2) =ᵐ[volume]
      fun x => ‖(factor a : ℂ) • f (a⁻¹ • x)‖^2 :=
    (action_ae ha f).fun_comp (fun z => ‖z‖^2)
  rw [integral_congr_ae he]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (factor_pos ha), mul_pow]
  rw [integral_const_mul]
  have hi := (inverse_measurePreserving ha).integral_comp
    (measurableEmbedding_const_smul₀ (inv_ne_zero ha.ne')) (fun p => ‖f p‖^2)
  change (∫ x, ‖f (a⁻¹ • x)‖^2) = _ at hi
  rw [hi, integral_smul_measure, ENNReal.toReal_ofReal (pow_pos ha _).le]
  change factor a ^ 2 * (a^3 * (∫ p, ‖f p‖^2)) = _
  rw [← mul_assoc, factor_square ha, one_mul, ← norm_sq]

theorem action_norm {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) : ‖action ha f‖ = ‖f‖ := by
  have he := action_norm_sq ha f
  nlinarith [norm_nonneg (action ha f), norm_nonneg f]

def linear {a : ℝ} (ha : 0 < a) : L2 (H := H) →ₗ[ℂ] L2 (H := H) where
  toFun := action ha
  map_add' f g := by
    apply Lp.ext
    filter_upwards [action_ae ha (f+g), action_ae ha f, action_ae ha g,
      inverse_ae ha (Lp.coeFn_add f g), Lp.coeFn_add (action ha f) (action ha g)]
      with x hfg hf hg hi ho
    simp only [hfg, ho, hi, Pi.add_apply, hf, hg, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [action_ae ha (c • f), action_ae ha f, inverse_ae ha (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (action ha f)] with x hcf hf hi ho
    change action ha (c • f) x = (c • action ha f) x
    simp only [hcf, ho, hi, Pi.smul_apply, hf, smul_smul, mul_comm]

def isometry {a : ℝ} (ha : 0 < a) : L2 (H := H) →ₗᵢ[ℂ] L2 (H := H) where
  toLinearMap := linear ha
  norm_map' := action_norm ha

theorem action_inverse {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) :
    action (inv_pos.mpr ha) (action ha f) = f := by
  apply Lp.ext
  have hi := inverse_ae (inv_pos.mpr ha) (action_ae ha f)
  filter_upwards [action_ae (inv_pos.mpr ha) (action ha f), hi] with x hx hi
  rw [hx, hi]
  simp only [inv_inv, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [← Complex.ofReal_mul, factor_inverse ha, Complex.ofReal_one, one_smul]

def equiv {a : ℝ} (ha : 0 < a) : L2 (H := H) ≃ₗᵢ[ℂ] L2 (H := H) :=
  LinearIsometryEquiv.ofSurjective (isometry ha) (fun f =>
    ⟨action (inv_pos.mpr ha) f, by
      change action ha (action (inv_pos.mpr ha) f) = f
      simpa only [inv_inv] using action_inverse (inv_pos.mpr ha) f⟩)

theorem equiv_ae {a : ℝ} (ha : 0 < a) (f : L2 (H := H)) :
    equiv ha f =ᵐ[volume] fun x => (factor a : ℂ) • f (a⁻¹ • x) := action_ae ha f

end Maxwell.Continuum.L2Dilation
