import Maxwell.Continuum.WellCutoffGevrey

/-! Finite almost-analytic Taylor extension in one real direction.
The Cauchy--Riemann defect is the exact last Taylor term, without
assuming that the compact cutoff is analytic. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex

def coefficient (j : ℕ) (s : ℝ) : ℂ := (I * (s : ℂ))^j / (j.factorial : ℂ)

def taylor (K : ℕ) (f : ℝ → ℝ) (x s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K+1), coefficient j s * ((iteratedDeriv j f x : ℝ) : ℂ)

theorem coefficient_zero (s : ℝ) : coefficient 0 s = 1 := by simp [coefficient]

theorem taylor_zero (f : ℝ → ℝ) (x s : ℝ) : taylor 0 f x s = (f x : ℂ) := by
  simp [taylor, coefficient]

theorem taylor_succ (K : ℕ) (f : ℝ → ℝ) (x s : ℝ) :
    taylor (K+1) f x s = taylor K f x s +
      coefficient (K+1) s * ((iteratedDeriv (K+1) f x : ℝ) : ℂ) := by
  exact Finset.sum_range_succ _ _

theorem coefficient_hasDerivAt_succ (j : ℕ) (s : ℝ) :
    HasDerivAt (coefficient (j+1)) (I * coefficient j s) s := by
  have hf := (((hasDerivAt_id s).ofReal_comp.const_mul I).pow (j+1)).div_const
    ((j+1).factorial : ℂ)
  convert hf using 1
  · rfl
  · simp only [coefficient, Nat.add_sub_cancel, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, id_eq, ofReal_one, mul_one]
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
    have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
    field_simp

theorem taylor_hasDerivAt_s (K : ℕ) (f : ℝ → ℝ) (x s : ℝ) :
    HasDerivAt (fun t => taylor K f x t)
      (I * ∑ j ∈ Finset.range K, coefficient j s * ((iteratedDeriv (j+1) f x : ℝ) : ℂ)) s := by
  induction K with
  | zero => simpa only [taylor_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
      using hasDerivAt_const s (f x : ℂ)
  | succ K ih =>
    have hd := ih.add ((coefficient_hasDerivAt_succ K s).mul_const
      ((iteratedDeriv (K+1) f x : ℝ) : ℂ))
    convert hd using 1
    · funext t
      exact taylor_succ K f x t
    · rw [Finset.sum_range_succ]
      ring

theorem taylor_hasDerivAt_x (K : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x s : ℝ) :
    HasDerivAt (fun y => taylor K f y s)
      (∑ j ∈ Finset.range (K+1), coefficient j s * ((iteratedDeriv (j+1) f x : ℝ) : ℂ)) x := by
  have hd (j : ℕ) (_ : j ∈ Finset.range (K+1)) :
      HasDerivAt (fun y => coefficient j s * ((iteratedDeriv j f y : ℝ) : ℂ))
        (coefficient j s * ((iteratedDeriv (j+1) f x : ℝ) : ℂ)) x := by
    have hj := ((hf.differentiable_iteratedDeriv j
      (by exact_mod_cast (ENat.natCast_lt_top j)) x).hasDerivAt).ofReal_comp
    simpa only [← iteratedDeriv_succ] using hj.const_mul (coefficient j s)
  convert HasDerivAt.sum hd using 1
  funext y
  simp only [taylor, Finset.sum_apply]

theorem taylor_defect (K : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x s : ℝ) :
    deriv (fun t => taylor K f x t) s - I * deriv (fun y => taylor K f y s) x =
      -I * coefficient K s * ((iteratedDeriv (K+1) f x : ℝ) : ℂ) := by
  rw [(taylor_hasDerivAt_s K f x s).deriv, (taylor_hasDerivAt_x K f hf x s).deriv,
    Finset.sum_range_succ]
  ring

theorem coefficient_norm (j : ℕ) (s : ℝ) :
    ‖coefficient j s‖ = |s|^j / (j.factorial : ℝ) := by
  simp only [coefficient, norm_div, norm_pow, norm_mul, norm_I, one_mul,
    norm_real, Real.norm_eq_abs, norm_natCast]

theorem taylor_defect_norm (K : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x s : ℝ) :
    ‖deriv (fun t => taylor K f x t) s - I * deriv (fun y => taylor K f y s) x‖ =
      (|s|^K / (K.factorial : ℝ)) * |iteratedDeriv (K+1) f x| := by
  rw [taylor_defect K f hf, norm_mul, norm_mul, norm_neg, norm_I,
    one_mul, coefficient_norm, norm_real, Real.norm_eq_abs]

end Maxwell.Continuum.AlmostAnalytic
