import Maxwell.Continuum.HighSchur

/-!
# Positive high-block elimination preserves strict parameter decrease

The effective low quadratic form is the attained minimum over the literal
high operator domain. Comparing the full quadratic forms at a minimizer
therefore preserves the coefficient of strict decrease on the low space.
-/

noncomputable section

namespace Maxwell.Continuum.HighSchur

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {L K : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- Positivity of the actual high quadratic form gives the lower norm bound. -/
theorem coercive_lower_bound (A : K →ₗ.[ℂ] K) {c : ℝ}
    (hcoercive : ∀ y : A.domain, c * ‖(y : K)‖ ^ 2 ≤ (inner ℂ (y : K) (A y)).re)
    (y : A.domain) : c * ‖(y : K)‖ ≤ ‖A y‖ := by
  have h := hcoercive y
  have hi := re_inner_le_norm (𝕜 := ℂ) (y : K) (A y)
  change (inner ℂ (y : K) (A y)).re ≤ ‖(y : K)‖ * ‖A y‖ at hi
  by_cases hy : ‖(y : K)‖ = 0
  · rw [hy, mul_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖(y : K)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    nlinarith

/-- A positive self-adjoint high block has a constructed bounded inverse. -/
def positiveInverse (A : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ y : A.domain, c * ‖(y : K)‖ ^ 2 ≤ (inner ℂ (y : K) (A y)).re) :
    BoundedInverse A :=
  BoundedInverse.ofLowerBound hA hc (coercive_lower_bound A hcoercive)

theorem positiveInverse_norm_le (A : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ y : A.domain, c * ‖(y : K)‖ ^ 2 ≤ (inner ℂ (y : K) (A y)).re) :
    ‖(positiveInverse A hA hc hcoercive).map‖ ≤ c⁻¹ :=
  inverse_opNorm_le A hc (coercive_lower_bound A hcoercive) hA

variable (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K} (R : BoundedInverse A)

theorem schur_symmetric (hD : D.IsSymmetric) (hA : IsSelfAdjoint A) :
    (schur D B R).IsSymmetric := by
  intro x y
  change inner ℂ (D x - B.adjoint (R.map (B x))) y =
    inner ℂ x (D y - B.adjoint (R.map (B y)))
  rw [inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact congrArg₂ (· - ·) (hD x y) ((R.map_selfAdjoint hA).isSymmetric (B x) (B y))

theorem schur_energy (x : L) :
    (inner ℂ x (schur D B R x)).re =
      (inner ℂ x (D x)).re - (inner ℂ (B x) (R.map (B x))).re := by
  rw [schur_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right, Complex.sub_re]

/-- The full-block quadratic form, written on the literal high domain. -/
def energy (x : L) (y : A.domain) : ℝ :=
  (inner ℂ x (D x)).re + 2 * (inner ℂ (B x) (y : K)).re +
    (inner ℂ (y : K) (A y)).re

def pairDomain (x : L) (y : A.domain) : domain (L := L) A :=
  ⟨WithLp.toLp 2 (x, (y : K)), y.property⟩

theorem energy_eq_block (x : L) (y : A.domain) :
    energy D B x y =
      (inner ℂ (pairDomain x y : Ambient L K) (block D B A (pairDomain x y))).re := by
  change _ = (inner ℂ x (D x + B.adjoint (y : K)) +
    inner ℂ (y : K) (B x + A y)).re
  rw [inner_add_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.add_re]
  have h := inner_re_symm (𝕜 := ℂ) (y : K) (B x)
  change (inner ℂ (y : K) (B x)).re = (inner ℂ (B x) (y : K)).re at h
  rw [h]
  unfold energy
  ring

omit [CompleteSpace K] in
/-- Completing the square for a possibly unbounded positive operator. -/
theorem inverse_variational (hA : A.IsFormalAdjoint A)
    (hpos : ∀ y : A.domain, 0 ≤ (inner ℂ (y : K) (A y)).re) (g : K) (y : A.domain) :
    2 * (inner ℂ g (y : K)).re - (inner ℂ (y : K) (A y)).re ≤
      (inner ℂ g (R.map g)).re := by
  let z : A.domain := ⟨R.map g, R.mem_domain g⟩
  have hz : A z = g := R.apply_map g
  have hn := hpos (y - z)
  change 0 ≤ (inner ℂ ((y : K) - (z : K)) (A (y - z))).re at hn
  have hzy : (inner ℂ (z : K) (A y)).re = (inner ℂ g (y : K)).re := by
    have h := hA z y
    rw [hz] at h
    exact congrArg Complex.re h.symm
  have hyg := inner_re_symm (𝕜 := ℂ) (y : K) g
  have hzg := inner_re_symm (𝕜 := ℂ) (z : K) g
  change (inner ℂ (y : K) g).re = (inner ℂ g (y : K)).re at hyg
  change (inner ℂ (z : K) g).re = (inner ℂ g (z : K)).re at hzg
  simp only [A.map_sub, hz, inner_sub_left, inner_sub_right, Complex.sub_re,
    hzy, hyg, hzg] at hn
  change 2 * (inner ℂ g (y : K)).re - (inner ℂ (y : K) (A y)).re ≤
    (inner ℂ g (z : K)).re
  linarith

/-- The Schur quadratic form is a lower bound for every high-domain completion. -/
theorem schur_energy_le (hA : A.IsFormalAdjoint A)
    (hpos : ∀ y : A.domain, 0 ≤ (inner ℂ (y : K) (A y)).re) (x : L) (y : A.domain) :
    (inner ℂ x (schur D B R x)).re ≤ energy D B x y := by
  have h := inverse_variational R hA hpos (B x) (-y)
  simp only [A.map_neg, Submodule.coe_neg, inner_neg_left, inner_neg_right,
    neg_neg, Complex.neg_re] at h
  rw [schur_energy]
  unfold energy
  linarith

/-- The minimizing high field is an actual vector of D(A). -/
def minimizer (x : L) : A.domain :=
  ⟨-R.map (B x), A.domain.neg_mem (R.mem_domain (B x))⟩

omit [CompleteSpace L] [CompleteSpace K] in
theorem minimizer_action (x : L) : A (minimizer B R x) = -B x := by
  change A (-⟨R.map (B x), R.mem_domain (B x)⟩) = -B x
  rw [A.map_neg, R.apply_map]

theorem energy_minimizer (x : L) :
    energy D B x (minimizer B R x) = (inner ℂ x (schur D B R x)).re := by
  rw [schur_energy]
  unfold energy
  rw [minimizer_action]
  change (inner ℂ x (D x)).re + 2 * (inner ℂ (B x) (-R.map (B x))).re +
    (inner ℂ (-R.map (B x)) (-B x)).re = _
  rw [inner_neg_left, inner_neg_right, inner_neg_right, neg_neg, Complex.neg_re]
  have h := inner_re_symm (𝕜 := ℂ) (R.map (B x)) (B x)
  change (inner ℂ (R.map (B x)) (B x)).re = (inner ℂ (B x) (R.map (B x))).re at h
  rw [h]
  ring

/-- Eliminating a positive high block preserves the full family's strict
decrease coefficient on the retained low space. -/
theorem schur_strict_decrease
    (D₁ D₂ : L →L[ℂ] L) (B₁ B₂ : L →L[ℂ] K)
    {A₁ A₂ : K →ₗ.[ℂ] K} (R₁ : BoundedInverse A₁) (R₂ : BoundedInverse A₂)
    (hdom : A₁.domain = A₂.domain) (hA₂ : A₂.IsFormalAdjoint A₂)
    (hpos₂ : ∀ y : A₂.domain, 0 ≤ (inner ℂ (y : K) (A₂ y)).re)
    {c : ℝ} (hc : 0 ≤ c)
    (hdecrease : ∀ (x : L) (y : A₁.domain),
      energy (A := A₂) D₂ B₂ x ⟨(y : K), hdom ▸ y.property⟩ ≤ energy D₁ B₁ x y -
        c * (‖x‖ ^ 2 + ‖(y : K)‖ ^ 2)) (x : L) :
    (inner ℂ x (schur D₂ B₂ R₂ x)).re ≤
      (inner ℂ x (schur D₁ B₁ R₁ x)).re - c * ‖x‖ ^ 2 := by
  let y := minimizer B₁ R₁ x
  have hv := schur_energy_le D₂ B₂ R₂ hA₂ hpos₂ x ⟨(y : K), hdom ▸ y.property⟩
  have hd := hdecrease x y
  have he := energy_minimizer D₁ B₁ R₁ x
  change energy D₁ B₁ x y = _ at he
  rw [he] at hd
  nlinarith [mul_nonneg hc (sq_nonneg ‖(y : K)‖)]

end Maxwell.Continuum.HighSchur
