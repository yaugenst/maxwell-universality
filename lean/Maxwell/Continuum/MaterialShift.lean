import Maxwell.Continuum.Operator
import Maxwell.Continuum.SelfAdjointResolventShift

/-!
# Literal uniform dielectric detuning

The shifted material is the measurable scalar function `ε(x) + σ`. The
upper material margin is explicit, and its multiplier is proved to be
exactly the original multiplier plus `σ I`.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace ScalarDielectric

variable (ε : ScalarDielectric) (σ : ℝ) (hσ : 0 ≤ σ)
variable (hupper : ∀ x, ε.coefficient x + σ ≤ 25)

/-- The actual uniformly shifted, still scalar and bounded dielectric. -/
def shifted : ScalarDielectric where
  coefficient x := ε.coefficient x + σ
  measurable := ε.measurable.add measurable_const
  lower x := (ε.lower x).trans (le_add_of_nonneg_right hσ)
  upper := hupper

@[simp] theorem shifted_coefficient (x : Space) :
    (ε.shifted σ hσ hupper).coefficient x = ε.coefficient x + σ := rfl

theorem shifted_scalarMultiplier_apply (u : ScalarL2) :
    (ε.shifted σ hσ hupper).scalarMultiplier u = ε.scalarMultiplier u + (σ : ℂ) • u := by
  apply Lp.ext
  filter_upwards [(ε.shifted σ hσ hupper).scalarProduct_ae u, ε.scalarProduct_ae u,
    Lp.coeFn_add (ε.scalarMultiplier u) ((σ : ℂ) • u), Lp.coeFn_smul (σ : ℂ) u]
    with x hs he ha hc
  change (ε.shifted σ hσ hupper).scalarProduct u x =
    (ε.scalarMultiplier u + (σ : ℂ) • u : ScalarL2) x
  rw [hs, ha]
  simp only [Pi.add_apply]
  rw [hc]
  change ((ε.coefficient x + σ : ℝ) : ℂ) * u x = ε.scalarProduct u x + (σ : ℂ) * u x
  rw [he, Complex.ofReal_add, add_mul]

theorem shifted_multiplier :
    (ε.shifted σ hσ hupper).multiplier =
      ε.multiplier + (σ : ℂ) • ContinuousLinearMap.id ℂ FieldL2 := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact ε.shifted_scalarMultiplier_apply σ hσ hupper (u i)

theorem shifted_domainMultiplier (Ω : Opens Space) :
    (ε.shifted σ hσ hupper).domainMultiplier Ω =
      ε.domainMultiplier Ω + (σ : ℂ) • ContinuousLinearMap.id ℂ (testL2Closure Ω) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change (ε.shifted σ hσ hupper).multiplier (u : FieldL2) =
    ε.multiplier (u : FieldL2) + (σ : ℂ) • (u : FieldL2)
  rw [ε.shifted_multiplier σ hσ hupper]
  rfl

/-- A unit of pointwise material margin accommodates every detuning in [0,1]. -/
theorem shifted_upper_of_margin (hmargin : ∀ x, ε.coefficient x ≤ 24)
    (hsmall : σ ≤ 1) : ∀ x, ε.coefficient x + σ ≤ 25 := by
  intro x
  linarith [hmargin x]

end ScalarDielectric

/-- Literal dielectric detuning equals the real shift of the actual Maxwell operator. -/
theorem maxwellOperator_shifted (Ω : Opens Space) (ε : ScalarDielectric)
    (σ : ℝ) (hσ : 0 ≤ σ) (hupper : ∀ x, ε.coefficient x + σ ≤ 25) :
    maxwellOperator Ω (ε.shifted σ hσ hupper) =
      SelfAdjointResolvent.shift (maxwellOperator Ω ε) σ := by
  refine LinearPMap.ext_iff.mpr ⟨rfl, ?_⟩
  intro x hx hy
  rw [maxwellOperator_apply, SelfAdjointResolvent.shift_apply, maxwellOperator_apply,
    ε.shifted_domainMultiplier σ hσ hupper Ω]
  change pecCurlCurl Ω ⟨x, hx⟩ - (ε.domainMultiplier Ω x + (σ : ℂ) • x) =
    pecCurlCurl Ω ⟨x, hy⟩ - ε.domainMultiplier Ω x - (σ : ℂ) • x
  abel

end Maxwell.Continuum
