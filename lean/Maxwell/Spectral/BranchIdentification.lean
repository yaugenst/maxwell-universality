import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

/-! Identification of an eigenvalue transported into another fiber family.
The local off-pole resolvent excludes any competing nearby eigenvalue. No
choice of eigenbasis, simplicity premise, or complex gauge is required. -/

namespace Maxwell.Spectral.BranchIdentification

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A genuine nonzero eigenvector makes its spectral shift noninvertible. -/
theorem not_isInvertible_of_eigenvector (T : H →L[ℂ] H) (value : ℂ)
    (v : H) (hv : v ≠ 0) (heigen : T v = value • v) :
    ¬ (T - value • (1 : H →L[ℂ] H)).IsInvertible := by
  intro hi
  apply hv
  apply hi.injective
  change T v - value • v = (T - value • (1 : H →L[ℂ] H)) 0
  rw [heigen, sub_self, map_zero]

variable {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]

/-- Pull back the joint momentum/spectral resolvent neighborhood along a
continuous candidate eigenvalue approaching the same center energy. The
eigenvectors themselves need not depend continuously on the parameter. -/
theorem eventuallyEq_of_offPole_invertible
    (A : W → H →L[ℂ] H) (fullValue : W → ℂ)
    (coordinates : X → W) (candidate : X → ℂ)
    (x₀ : X) (w₀ : W) (energy : ℂ)
    (hcoordinates : Tendsto coordinates (𝓝 x₀) (𝓝 w₀))
    (hcandidate : Tendsto candidate (𝓝 x₀) (𝓝 energy))
    (hresolvent : ∀ᶠ z in 𝓝 (w₀, (0 : ℂ)),
      fullValue z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • (1 : H →L[ℂ] H)).IsInvertible)
    (heigen : ∀ᶠ x in 𝓝 x₀, ∃ v : H, v ≠ 0 ∧ A (coordinates x) v = candidate x • v) :
    (fun x => fullValue (coordinates x)) =ᶠ[𝓝 x₀] candidate := by
  have hshift : Tendsto (fun x => candidate x - energy) (𝓝 x₀) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using hcandidate.sub (tendsto_const_nhds (x := energy))
  have hpair : Tendsto (fun x => (coordinates x, candidate x - energy))
      (𝓝 x₀) (𝓝 (w₀, (0 : ℂ))) := hcoordinates.prodMk_nhds hshift
  filter_upwards [hpair.eventually hresolvent, heigen] with x hinv ⟨v, hv, hTv⟩
  by_contra hne
  have hc : energy + (candidate x - energy) = candidate x := by abel
  have hi : (A (coordinates x) - candidate x • (1 : H →L[ℂ] H)).IsInvertible := by
    simpa only [hc] using hinv (by simpa only [hc] using hne)
  exact not_isInvertible_of_eigenvector _ _ v hv hTv hi

/-- The common application has an explicit continuous candidate branch and
a supplied nonzero eigenvector at each nearby real parameter. -/
theorem eventuallyEq_of_continuous_eigenpair
    (A : W → H →L[ℂ] H) (fullValue : W → ℂ)
    (coordinates : X → W) (candidate : X → ℂ) (vector : X → H)
    (x₀ : X) (w₀ : W) (energy : ℂ)
    (hcoordinates : Tendsto coordinates (𝓝 x₀) (𝓝 w₀))
    (hcandidate : ContinuousAt candidate x₀) (hcenter : candidate x₀ = energy)
    (hresolvent : ∀ᶠ z in 𝓝 (w₀, (0 : ℂ)),
      fullValue z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • (1 : H →L[ℂ] H)).IsInvertible)
    (hnonzero : ∀ᶠ x in 𝓝 x₀, vector x ≠ 0)
    (heigen : ∀ᶠ x in 𝓝 x₀, A (coordinates x) (vector x) = candidate x • vector x) :
    (fun x => fullValue (coordinates x)) =ᶠ[𝓝 x₀] candidate := by
  apply eventuallyEq_of_offPole_invertible A fullValue coordinates candidate x₀ w₀ energy
    hcoordinates (by simpa only [hcenter] using hcandidate.tendsto) hresolvent
  filter_upwards [hnonzero, heigen] with x hx he
  exact ⟨vector x, hx, he⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A fiber intertwining transports the candidate eigenvector into the full
family. Injectivity of the actual folding map preserves nonvanishing. -/
theorem eventuallyEq_of_injective_intertwining
    (A : W → H →L[ℂ] H) (B : X → V →L[ℂ] V) (fullValue : W → ℂ)
    (coordinates : X → W) (candidate : X → ℂ) (vector : X → V)
    (folding : X → V →ₗ[ℂ] H) (x₀ : X) (w₀ : W) (energy : ℂ)
    (hcoordinates : Tendsto coordinates (𝓝 x₀) (𝓝 w₀))
    (hcandidate : ContinuousAt candidate x₀) (hcenter : candidate x₀ = energy)
    (hresolvent : ∀ᶠ z in 𝓝 (w₀, (0 : ℂ)),
      fullValue z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • (1 : H →L[ℂ] H)).IsInvertible)
    (hinjective : ∀ᶠ x in 𝓝 x₀, Function.Injective (folding x))
    (hintertwine : ∀ᶠ x in 𝓝 x₀, ∀ v,
      A (coordinates x) (folding x v) = folding x (B x v))
    (hnonzero : ∀ᶠ x in 𝓝 x₀, vector x ≠ 0)
    (heigen : ∀ᶠ x in 𝓝 x₀, B x (vector x) = candidate x • vector x) :
    (fun x => fullValue (coordinates x)) =ᶠ[𝓝 x₀] candidate := by
  apply eventuallyEq_of_continuous_eigenpair A fullValue coordinates candidate
    (fun x => folding x (vector x)) x₀ w₀ energy hcoordinates hcandidate hcenter hresolvent
  · filter_upwards [hinjective, hnonzero] with x hinj hne
    intro hz
    apply hne
    apply hinj
    simpa only [map_zero] using hz
  · filter_upwards [hintertwine, heigen] with x hinter he
    rw [hinter, he, map_smul]

/-- Neighborhood equality along real coordinates transfers both real ray
derivatives. Analyticity and differentiability need not be assumed again. -/
theorem real_ray_derivatives_eq {f g : X → ℂ} {x₀ : X}
    (heq : f =ᶠ[𝓝 x₀] g) (ray : ℝ → X)
    (hray : Tendsto ray (𝓝 (0 : ℝ)) (𝓝 x₀)) :
    deriv (fun t : ℝ => f (ray t)) 0 = deriv (fun t : ℝ => g (ray t)) 0 ∧
    deriv (deriv (fun t : ℝ => f (ray t))) 0 =
      deriv (deriv (fun t : ℝ => g (ray t))) 0 := by
  have hr : (fun t : ℝ => f (ray t)) =ᶠ[𝓝 (0 : ℝ)] fun t => g (ray t) :=
    hray.eventually heq
  exact ⟨hr.deriv_eq, hr.deriv.deriv_eq⟩

end Maxwell.Spectral.BranchIdentification
