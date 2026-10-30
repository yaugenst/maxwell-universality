import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual periodic Fourier coefficient bounds from iterated real derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open AddCircle MeasureTheory Set

def derivativeCoefficient (f : ℝ → ℂ) (K : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (iteratedDeriv K f) n

theorem derivativeCoefficient_bound (f : ℝ → ℂ) (K : ℕ) (n : ℤ) {B : ℝ}
    (hB : ∀ x, ‖iteratedDeriv K f x‖ ≤ B) : ‖derivativeCoefficient f K n‖ ≤ B := by
  unfold derivativeCoefficient
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs, sub_zero,
    abs_of_pos (by positivity : 0 < 1/(2*Real.pi))]
  have hi : ‖∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi)) • iteratedDeriv K f x‖ ≤ B*(2*Real.pi) := by
    have hh : ‖∫ x in (0 : ℝ)..2*Real.pi,
        fourier (-n) (x : AddCircle (2*Real.pi)) • iteratedDeriv K f x‖ ≤ B*|2*Real.pi-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
        exact hB x)
    simpa only [sub_zero, abs_of_pos Real.two_pi_pos] using hh
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))).trans_eq
  field_simp

theorem periodic_iteratedDeriv {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi)) (K : ℕ) :
    Function.Periodic (iteratedDeriv K f) (2*Real.pi) := by
  have he : (fun x => f (x+2*Real.pi))=f := funext hp
  intro x
  have h := congrArg (fun g : ℝ → ℂ => iteratedDeriv K g x) he
  simpa only [iteratedDeriv_comp_add_const] using h

theorem derivativeCoefficient_step {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2*Real.pi)) (K : ℕ) {n : ℤ} (hn : n≠0) :
    Complex.I*(n : ℂ)*derivativeCoefficient f K n=derivativeCoefficient f (K+1) n := by
  have hd (x : ℝ) : HasDerivAt (iteratedDeriv K f) (iteratedDeriv (K+1) f x) x := by
    have hc : ContDiff ℝ (K+1) f := hf.of_le (by simp)
    simpa only [iteratedDeriv_succ] using ((hc.differentiable_iteratedDeriv' K) x).hasDerivAt
  have hi : IntervalIntegrable (iteratedDeriv (K+1) f) volume 0 (2*Real.pi) :=
    (hf.continuous_iteratedDeriv (K+1) (by simp)).intervalIntegrable _ _
  have hb : iteratedDeriv K f (2*Real.pi)=iteratedDeriv K f 0 := by
    simpa only [zero_add] using periodic_iteratedDeriv hp K 0
  have h := fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn (fun x _ => hd x) hi
  simp only [hb, sub_self, mul_zero, zero_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_zero, sub_zero] at h
  change derivativeCoefficient f K n=_ at h
  rw [h]
  change Complex.I*(n : ℂ)*(1/(-2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*
    (-((2*(Real.pi : ℂ))*derivativeCoefficient f (K+1) n)))=_
  field_simp

theorem derivativeCoefficient_iterated_norm {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2*Real.pi)) {n : ℤ} (hn : n≠0) (K : ℕ) :
    ‖derivativeCoefficient f K n‖=|(n : ℝ)|^K*‖derivativeCoefficient f 0 n‖ := by
  induction K with
  | zero => simp only [pow_zero, one_mul]
  | succ K ih =>
    rw [← derivativeCoefficient_step hf hp K hn, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_intCast, one_mul, ih, pow_succ]
    ring

theorem factorial_decay_optimization (n : ℕ) {A B : ℝ} (hB : 0≤B)
    (hb : ∀ K : ℕ, (n : ℝ)^K*A ≤ (K.factorial : ℝ)*B) :
    A ≤ B*(1/2 : ℝ)^(n/2) := by
  by_cases hn : n=0
  · subst n
    simpa only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
      Nat.zero_div, mul_one] using hb 0
  have hn0 : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hfact : ((n/2).factorial : ℝ) ≤ (n/2 : ℕ)^(n/2) := by exact_mod_cast Nat.factorial_le_pow (n/2)
  have hdiv : ((n/2 : ℕ) : ℝ) ≤ (n : ℝ)/2 := by
    have hi : 2*(n/2) ≤ n := Nat.mul_div_le n 2
    have hr : (2 : ℝ)*((n/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
    linarith
  have hp : ((n/2 : ℕ) : ℝ)^(n/2) ≤ ((n : ℝ)/2)^(n/2) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv _
  have h := (hb (n/2)).trans (mul_le_mul_of_nonneg_right (hfact.trans hp) hB)
  have he : ((n : ℝ)/2)^(n/2)*B=(n : ℝ)^(n/2)*(B*(1/2 : ℝ)^(n/2)) := by
    rw [show (n : ℝ)/2=(n : ℝ)*(1/2) by ring, mul_pow]
    ring
  rw [he] at h
  exact (mul_le_mul_iff_right₀ (pow_pos hn0 _)).mp h

#print axioms derivativeCoefficient_iterated_norm
#print axioms factorial_decay_optimization

end Maxwell.Continuum.Profile
