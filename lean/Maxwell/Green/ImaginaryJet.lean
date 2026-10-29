import Maxwell.Green.ComplexCoercivity
import Maxwell.Green.PrincipalChart
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The real gradient and Hessian at an imaginary support point follow
from the actual local conjugation symmetry and analytic derivatives. -/

noncomputable section

open Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace

namespace Maxwell.Green

theorem odd_second_derivative_zero (f : ℝ → ℝ)
    (hodd : (fun t => f (-t)) =ᶠ[𝓝 (0 : ℝ)] fun t => -f t) :
    iteratedDeriv 2 f 0 = 0 := by
  have h := hodd.iteratedDeriv_eq 2
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at h
  norm_num at h
  linarith

theorem imaginary_point_first_real_zero
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    (hlam : AnalyticAt ℂ lam (Complex.I • complexifyCoordinates β))
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • complexifyCoordinates β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ((fderiv ℂ lam (Complex.I • complexifyCoordinates β)) (complexifyCoordinates q)).re = 0 := by
  have hline : Tendsto (complexRealLine q β) (𝓝 (0 : ℝ))
      (𝓝 (Complex.I • complexifyCoordinates β)) := by
    simpa only [complexRealLine_zero] using
      ((continuous_complexRealLine q β).continuousAt (x := (0 : ℝ))).tendsto
  have heven : (fun t => (lam (complexRealLine q β (-t))).re) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (lam (complexRealLine q β t)).re) := by
    filter_upwards [hline.eventually hreflection] with t ht
    have h := congrArg Complex.re ht
    simpa only [reflected_complexRealLine, Complex.conj_re] using h
  have hd := hasDerivAt_realPart_line lam q β 0 (by simpa only [complexRealLine_zero] using hlam)
  exact even_hasDerivAt_zero (f := fun t => (lam (complexRealLine q β t)).re)
    (by simpa only [complexRealLine_zero] using hd) heven

theorem hasDerivAt_imagPart_line
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates) (t : ℝ)
    (hlam : AnalyticAt ℂ lam (complexRealLine q β t)) :
    HasDerivAt (fun u => (lam (complexRealLine q β u)).im)
      ((fderiv ℂ lam (complexRealLine q β t)) (complexifyCoordinates q)).im t := by
  have h := (hlam.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_complexRealLine q β t)
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_imagPart_line_derivative
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates) (t : ℝ)
    (hlam : AnalyticAt ℂ lam (complexRealLine q β t)) :
    HasDerivAt
      (fun u => ((fderiv ℂ lam (complexRealLine q β u)) (complexifyCoordinates q)).im)
      ((complexHessian lam (complexRealLine q β t))
        (complexifyCoordinates q) (complexifyCoordinates q)).im t := by
  have h := (hlam.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_complexRealLine q β t)
  have he := ((ContinuousLinearMap.apply ℂ ℂ (complexifyCoordinates q)).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t h
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t he

theorem imaginary_point_second_imag_zero
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    (hlam : AnalyticAt ℂ lam (Complex.I • complexifyCoordinates β))
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • complexifyCoordinates β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ((complexHessian lam (Complex.I • complexifyCoordinates β))
      (complexifyCoordinates q) (complexifyCoordinates q)).im = 0 := by
  let f : ℝ → ℝ := fun t => (lam (complexRealLine q β t)).im
  let df : ℝ → ℝ := fun t => ((fderiv ℂ lam (complexRealLine q β t)) (complexifyCoordinates q)).im
  have hline : Tendsto (complexRealLine q β) (𝓝 (0 : ℝ))
      (𝓝 (Complex.I • complexifyCoordinates β)) := by
    simpa only [complexRealLine_zero] using
      ((continuous_complexRealLine q β).continuousAt (x := (0 : ℝ))).tendsto
  have hodd : (fun t => f (-t)) =ᶠ[𝓝 (0 : ℝ)] fun t => -f t := by
    filter_upwards [hline.eventually hreflection] with t ht
    have h := congrArg Complex.im ht
    simpa only [f, reflected_complexRealLine, Complex.conj_im] using h
  have hderiv : deriv f =ᶠ[𝓝 (0 : ℝ)] df := by
    filter_upwards [hline.eventually hlam.eventually_analyticAt] with t ht
    exact (hasDerivAt_imagPart_line lam q β t ht).deriv
  have hsecond := hasDerivAt_imagPart_line_derivative lam q β 0
    (by simpa only [complexRealLine_zero] using hlam)
  have h := odd_second_derivative_zero f hodd
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq, hsecond.deriv] at h
  simpa only [complexRealLine_zero] using h

def imaginaryLevel (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) : RealTorusCoordinates → ℝ :=
  fun β => edge - (lam (Complex.I • complexifyCoordinates β)).re

theorem imaginaryLevel_directional_derivative
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β q : RealTorusCoordinates)
    (hlam : AnalyticAt ℂ lam (Complex.I • complexifyCoordinates β)) :
    (fderiv ℝ (imaginaryLevel lam edge) β) q =
      ((fderiv ℂ lam (Complex.I • complexifyCoordinates β)) (complexifyCoordinates q)).im := by
  let J : RealTorusCoordinates →L[ℝ] ComplexTorusCoordinates := Complex.I • complexifyCLM
  have h := (hlam.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp β J.hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp β h).const_sub edge
  have he := congrArg (fun L : RealTorusCoordinates →L[ℝ] ℝ => L q) hr.fderiv
  change (fderiv ℝ (fun x => edge - (lam (Complex.I • complexifyCoordinates x)).re) β) q = _
  simpa [J, map_smul] using he

theorem imaginary_point_gradient_identity
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β : RealTorusCoordinates)
    (hlam : AnalyticAt ℂ lam (Complex.I • complexifyCoordinates β))
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • complexifyCoordinates β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) (q : RealTorusCoordinates) :
    (fderiv ℂ lam (Complex.I • complexifyCoordinates β)) (complexifyCoordinates q) =
      Complex.I * ((fderiv ℝ (imaginaryLevel lam edge) β) q : ℂ) := by
  apply Complex.ext
  · simpa using imaginary_point_first_real_zero lam q β hlam hreflection
  · simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, zero_mul,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
    exact (imaginaryLevel_directional_derivative lam edge β q hlam).symm

def momentumCoordinates : MomentumSpace →L[ℝ] RealTorusCoordinates :=
  LinearMap.toContinuousLinearMap {
    toFun := WithLp.ofLp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def momentumComplexCLM : MomentumSpace →L[ℝ] ComplexTorusCoordinates :=
  complexifyCLM.comp momentumCoordinates

@[simp] theorem complexify_momentumCoordinates (x : MomentumSpace) :
    complexifyCoordinates (momentumCoordinates x) = momentumComplex x := by
  ext j
  rfl

@[simp] theorem momentumComplexCLM_apply (x : MomentumSpace) :
    momentumComplexCLM x = momentumComplex x := rfl

def momentumHessian (lam : ComplexTorusCoordinates → ℂ) (center : ComplexTorusCoordinates) :
    MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ MomentumSpace ℂ ℝ Complex.reCLM).comp
    (((complexHessian lam center).bilinearRestrictScalars ℝ).bilinearComp
      momentumComplexCLM momentumComplexCLM)

@[simp] theorem momentumHessian_apply (lam : ComplexTorusCoordinates → ℂ)
    (center : ComplexTorusCoordinates) (x y : MomentumSpace) :
    momentumHessian lam center x y =
      ((complexHessian lam center) (momentumComplex x) (momentumComplex y)).re := rfl

theorem momentumHessian_symmetric (lam : ComplexTorusCoordinates → ℂ)
    (center : ComplexTorusCoordinates) (hlam : AnalyticAt ℂ lam center) :
    ∀ x y, momentumHessian lam center x y = momentumHessian lam center y x := by
  intro x y
  have hs := hlam.contDiffAt.isSymmSndFDerivAt_of_omega
  exact congrArg Complex.re (hs.eq (momentumComplex x) (momentumComplex y))

theorem imaginary_momentumHessian_binding
    (lam : ComplexTorusCoordinates → ℂ) (β : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β))
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • momentumComplex β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) (x : MomentumSpace) :
    (fderiv ℂ (fderiv ℂ lam) (Complex.I • momentumComplex β))
      (momentumComplex x) (momentumComplex x) =
      (momentumHessian lam (Complex.I • momentumComplex β) x x : ℂ) := by
  apply Complex.ext
  · rfl
  · change ((complexHessian lam (Complex.I • momentumComplex β))
      (momentumComplex x) (momentumComplex x)).im = 0
    exact imaginary_point_second_imag_zero lam (momentumCoordinates x)
      (momentumCoordinates β) hlam hreflection

def imaginaryMomentumLevel (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) : MomentumSpace → ℝ :=
  fun β => edge - (lam (Complex.I • momentumComplex β)).re

theorem imaginaryMomentumLevel_directional_derivative
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β x : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β)) :
    (fderiv ℝ (imaginaryMomentumLevel lam edge) β) x =
      ((fderiv ℂ lam (Complex.I • momentumComplex β)) (momentumComplex x)).im := by
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := Complex.I • momentumComplexCLM
  have h := (hlam.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp β J.hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp β h).const_sub edge
  have he := congrArg (fun L : MomentumSpace →L[ℝ] ℝ => L x) hr.fderiv
  change (fderiv ℝ (fun z => edge - (lam (Complex.I • momentumComplex z)).re) β) x = _
  simpa [J, map_smul] using he

/-- The level-set gradient obtained at the actual support point is exactly
the imaginary spectral derivative used in the normal coordinate. -/
theorem imaginary_momentum_gradient_binding
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β g : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β))
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • momentumComplex β),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hgradient : HasFDerivAt (imaginaryMomentumLevel lam edge) (innerSL ℝ g) β)
    (x : MomentumSpace) :
    (fderiv ℂ lam (Complex.I • momentumComplex β)) (momentumComplex x) =
      Complex.I * (inner ℝ g x : ℂ) := by
  apply Complex.ext
  · simpa only [complexify_momentumCoordinates, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self] using
      imaginary_point_first_real_zero lam (momentumCoordinates x)
      (momentumCoordinates β) hlam hreflection
  · simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, zero_mul,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
    have h := imaginaryMomentumLevel_directional_derivative lam edge β x hlam
    rw [hgradient.fderiv] at h
    exact h.symm

theorem imaginary_momentum_value_real
    (lam : ComplexTorusCoordinates → ℂ) (β : MomentumSpace)
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • momentumComplex β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    (lam (Complex.I • momentumComplex β)).im = 0 := by
  have hfix : reflectedComplexCoordinates (Complex.I • momentumComplex β) =
      Complex.I • momentumComplex β := by
    ext j
    simp [reflectedComplexCoordinates, momentumComplex]
  have h := hreflection.self_of_nhds
  rw [hfix] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem imaginary_momentum_on_level
    (lam : ComplexTorusCoordinates → ℂ) (β : MomentumSpace) (edge ξ : ℝ)
    (hreflection : ∀ᶠ z in 𝓝 (Complex.I • momentumComplex β),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hlevel : imaginaryMomentumLevel lam edge β = ξ) :
    lam (Complex.I • momentumComplex β) = ((edge - ξ : ℝ) : ℂ) := by
  apply Complex.ext
  · change (lam (Complex.I • momentumComplex β)).re = edge - ξ
    dsimp [imaginaryMomentumLevel] at hlevel
    linarith
  · exact imaginary_momentum_value_real lam β hreflection

end Maxwell.Green
