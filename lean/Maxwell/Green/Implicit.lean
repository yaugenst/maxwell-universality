import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Analytic implicit roots from an analytic denominator and a nonzero normal
derivative. The root is constructed by the inverse function theorem. -/

noncomputable section

namespace Maxwell.Green

open Filter
open scoped Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- The implicit root constructed by the Banach-space implicit function
theorem is analytic when the original denominator is analytic. -/
theorem analyticAt_implicitFunctionOfProdDomain
    {D : W × ℂ → ℂ} {D' : W × ℂ →L[ℂ] ℂ} {z₀ : W × ℂ}
    (hD : AnalyticAt ℂ D z₀) (hd : HasStrictFDerivAt D D' z₀)
    (hi : (D' ∘L ContinuousLinearMap.inr ℂ W ℂ).IsInvertible) :
    AnalyticAt ℂ (hd.implicitFunctionOfProdDomain hi) z₀.1 := by
  let φ := hd.implicitFunctionDataOfProdDomain hi
  have ha : AnalyticAt ℂ φ.toOpenPartialHomeomorph φ.pt := hD.prod analyticAt_fst
  have hs := φ.toOpenPartialHomeomorph.analyticAt_symm'
    φ.pt_mem_toOpenPartialHomeomorph_source ha φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hpair : AnalyticAt ℂ (fun x : W => (D z₀, x)) z₀.1 :=
    analyticAt_const.prod analyticAt_id
  exact analyticAt_snd.comp (hs.comp_of_eq hpair rfl)

/-- A complex-linear endomorphism of the scalar field is multiplication by
its value on one. -/
theorem complex_linearMap_apply (L : ℂ →L[ℂ] ℂ) (z : ℂ) : L z = L 1 * z := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul z 1

theorem complex_linearMap_eq_smul_id (L : ℂ →L[ℂ] ℂ) :
    L = L 1 • ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext
  intro z
  exact complex_linearMap_apply L z

theorem complex_linearMap_isInvertible (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) :
    L.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    rw [complex_linearMap_apply L ((L 1)⁻¹ • z)]
    simp [smul_eq_mul, hL]
  · apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    rw [complex_linearMap_apply L z]
    simp [smul_eq_mul, hL]

theorem complex_linearMap_inverse_apply (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) (z : ℂ) :
    L.inverse z = (L 1)⁻¹ * z := by
  apply (complex_linearMap_isInvertible L hL).inverse_apply_eq.mpr
  rw [complex_linearMap_apply L ((L 1)⁻¹ * z)]
  simp [hL]

omit [CompleteSpace W] in
/-- The nonzero normal derivative persists on a full neighborhood, so the
local zero graph remains a simple normal zero. -/
theorem eventually_normal_derivative_ne_zero (D : W × ℂ → ℂ)
    (hD : AnalyticAt ℂ D (0, 0)) (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) :
    ∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), (fderiv ℂ D z) (0, 1) ≠ 0 := by
  have hc : ContinuousAt (fun z : W × ℂ => (fderiv ℂ D z) (0, 1)) (0, 0) :=
    hD.fderiv.continuousAt.clm_apply continuousAt_const
  exact hc.eventually (eventually_ne_nhds hu)

/-- An analytic denominator with a nonzero normal derivative has a locally
unique analytic zero graph. Its derivative is the exact implicit derivative.
No root function or analytic continuation of a root is assumed. -/
theorem exists_analytic_implicit_root
    (D : W × ℂ → ℂ) (hD : AnalyticAt ℂ D (0, 0)) (hzero : D (0, 0) = 0)
    (hu : (fderiv ℂ D (0, 0)) (0, 1) ≠ 0) :
    ∃ p : W → ℂ,
      p 0 = 0 ∧ AnalyticAt ℂ p 0 ∧
      (∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), D z = 0 ↔ p z.1 = z.2) ∧
      HasStrictFDerivAt p
        (-( (fderiv ℂ D (0, 0)) (0, 1))⁻¹ •
          (fderiv ℂ D (0, 0) ∘L ContinuousLinearMap.inl ℂ W ℂ)) 0 := by
  let D' := fderiv ℂ D (0, 0)
  have hd : HasStrictFDerivAt D D' (0, 0) := hD.hasStrictFDerivAt
  have hi : (D' ∘L ContinuousLinearMap.inr ℂ W ℂ).IsInvertible :=
    complex_linearMap_isInvertible _ hu
  let p := hd.implicitFunctionOfProdDomain hi
  have hp₀ : p 0 = 0 :=
    (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi).self_of_nhds.mp rfl
  refine ⟨p, hp₀, analyticAt_implicitFunctionOfProdDomain hD hd hi, ?_, ?_, ?_⟩
  · simpa only [hzero] using hd.eventually_apply_implicitFunctionOfProdDomain hi
  · simpa only [hzero] using hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi
  · have hp := hd.hasStrictFDerivAt_implicitFunctionOfProdDomain hi
    convert hp using 1
    ext w
    simp only [smul_apply, neg_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [complex_linearMap_inverse_apply _ hu]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    ring

end Maxwell.Green
