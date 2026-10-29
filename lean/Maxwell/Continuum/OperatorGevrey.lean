import Maxwell.Continuum.OperatorFourierDecay
import Maxwell.Continuum.WellCutoffGevrey
import Mathlib.Analysis.Complex.RealDeriv

/-! Real directional derivatives and the Gevrey product estimate for
Banach-valued symbols. -/

noncomputable section

namespace Maxwell.Continuum.OperatorFourier

open Set Filter Metric
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem directionalDerivative_eq_line (K : ℕ) (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y v : Space) :
    directionalDerivative K f y v = iteratedDeriv K (fun t : ℝ => f (y + t • v)) 0 := by
  let L : ℝ →L[ℝ] Space := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space => f (y + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have h := L.iteratedFDeriv_comp_right hg 0 (i := K) (by simp)
  have he : (fun z : Space => f (y + z)) ∘ L = (fun t : ℝ => f (y + t • v)) := rfl
  rw [he] at h
  rw [iteratedDeriv, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [L, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, zero_smul, one_smul]
  rw [iteratedFDeriv_comp_add_left, add_zero]
  rfl

theorem iteratedDeriv_restrict_complex [CompleteSpace F] (f : ℂ → F) (U : Set ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (K : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ U) :
    iteratedDeriv K (fun t : ℝ => f t) x = iteratedDeriv K f x := by
  induction K generalizing x with
  | zero => simp
  | succ K ih =>
    have he : iteratedDeriv K (fun t : ℝ => f t) =ᶠ[𝓝 x]
        (fun t : ℝ => iteratedDeriv K f t) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hmem] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have ha : AnalyticAt ℂ (iteratedDeriv K f) (x : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using (hf.iterated_deriv K) x hx
    have hd := ha.differentiableAt.hasDerivAt.scomp x Complex.ofRealCLM.hasDerivAt
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_smul, iteratedDeriv_succ] using hd.deriv

theorem gevrey_smul (f : ℝ → ℝ) (g : ℝ → F)
    (x : ℝ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (Cf Cg R : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hR : 0 ≤ R)
    (hfb : ∀ n : ℕ, |iteratedDeriv n f x| ≤ Cf * R ^ n * (n.factorial : ℝ) ^ 2)
    (hgb : ∀ n : ℕ, ‖iteratedDeriv n g x‖ ≤ Cg * R ^ n * (n.factorial : ℝ) ^ 2)
    (K : ℕ) :
    ‖iteratedDeriv K (fun t => f t • g t) x‖ ≤
      (Cf * Cg) * (2 * R) ^ K * (K.factorial : ℝ) ^ 2 := by
  have he := iteratedDerivWithin_smul (s := Set.univ) (x := x) (n := K)
    (Set.mem_univ x) uniqueDiffOn_univ
    (hf.of_le (by simp)).contDiffWithinAt (hg.of_le (by simp)).contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change iteratedDeriv K (fun t => f t • g t) x = _ at he
  rw [he]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (K + 1)) :
      ‖K.choose i • iteratedDeriv i f x • iteratedDeriv (K - i) g x‖ ≤
        Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 := by
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast,
      norm_smul, Real.norm_eq_abs, ← mul_assoc]
    calc
      (K.choose i : ℝ) * |iteratedDeriv i f x| * ‖iteratedDeriv (K - i) g x‖ ≤
          (K.choose i : ℝ) * (Cf * R ^ i * (i.factorial : ℝ) ^ 2) *
            (Cg * R ^ (K - i) * ((K - i).factorial : ℝ) ^ 2) := by
        gcongr
        · exact hfb i
        · exact hgb (K - i)
      _ = (Cf * Cg * R ^ K) *
          ((K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2) := by
        have hp : R ^ i * R ^ (K - i) = R ^ K := by rw [← pow_add, Nat.add_sub_of_le hiK]
        calc
          _ = (Cf * Cg * (R ^ i * R ^ (K - i))) *
              ((K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2) := by ring
          _ = _ := by rw [hp]
      _ ≤ Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (Well.factorial_split_bound K i hiK) (by positivity)
  calc
    ‖∑ i ∈ Finset.range (K + 1),
        K.choose i • iteratedDeriv i f x • iteratedDeriv (K - i) g x‖ ≤
        ∑ i ∈ Finset.range (K + 1),
          ‖K.choose i • iteratedDeriv i f x • iteratedDeriv (K - i) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (K + 1), Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = (K + 1 : ℝ) * (Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2) := by simp
    _ ≤ (2 : ℝ) ^ K * (Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := K))
    _ = (Cf * Cg) * (2 * R) ^ K * (K.factorial : ℝ) ^ 2 := by rw [mul_pow]; ring

end Maxwell.Continuum.OperatorFourier
