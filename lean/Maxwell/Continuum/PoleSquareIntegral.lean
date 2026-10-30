import Maxwell.Continuum.LaplaceFourier

/-! The exact absolutely convergent squared-pole integral, with the
angular Fourier normalization used by the continuum residue calculation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology FourierTransform

def oscillatoryPhase (T u : ℝ) : ℂ := Complex.exp (((T*u : ℝ) : ℂ)*I)

def poleSquare (p : ℂ) (u : ℝ) : ℂ := 1/((u : ℂ)-p)^2

theorem oscillatoryPhase_norm (T u : ℝ) : ‖oscillatoryPhase T u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem squareKernel_angular_integral {a : ℂ} (ha : a.re < 0) {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, oscillatoryPhase T u * squareKernel a u) =
      ((2*Real.pi*T : ℝ) : ℂ)*Complex.exp (a*T) := by
  let f : ℝ → ℂ := fun u => oscillatoryPhase T u*squareKernel a u
  have he : (∫ u : ℝ, f (2*Real.pi*u)) = (T : ℂ)*Complex.exp (a*T) := by
    convert squareKernel_fourier_inversion ha hT using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp only [f, oscillatoryPhase]
      congr 2
      push_cast
      ring
  rw [Measure.integral_comp_mul_left f (2*Real.pi),
    abs_of_pos (inv_pos.mpr (show 0 < (2*Real.pi : ℝ) by positivity))] at he
  have hh := congrArg (fun v : ℂ => ((2*Real.pi : ℝ) : ℂ)*v) he
  have hc : (((2*Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (show (2*Real.pi : ℝ) ≠ 0 by positivity)
  simp only [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul] at hh
  simpa only [f, Complex.ofReal_mul] using hh

theorem squareKernel_pole (p : ℂ) (u : ℝ) : squareKernel (I*p) u = -poleSquare p u := by
  have he : I*p-(u : ℂ)*I = -I*((u : ℂ)-p) := by ring
  rw [squareKernel, he, mul_pow, show (-I)^2=(-1 : ℂ) by norm_num,
    neg_one_mul, div_neg, poleSquare]

theorem poleSquare_integrable {p : ℂ} (hp : 0 < p.im) : Integrable (poleSquare p) := by
  have ha : (I*p).re < 0 := by simpa only [Complex.I_mul_re] using neg_neg_of_pos hp
  have he : poleSquare p = fun u => -squareKernel (I*p) u := by
    funext u
    rw [squareKernel_pole, neg_neg]
  rw [he]
  exact (squareKernel_integrable ha).neg

theorem oscillatory_poleSquare_integrable {p : ℂ} (hp : 0 < p.im) (T : ℝ) :
    Integrable (fun u => oscillatoryPhase T u*poleSquare p u) := by
  have hi := poleSquare_integrable hp
  have hc : Continuous (oscillatoryPhase T) := by unfold oscillatoryPhase; fun_prop
  apply hi.norm.mono' (hc.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun u => by
    change ‖oscillatoryPhase T u * poleSquare p u‖ ≤ ‖poleSquare p u‖
    rw [norm_mul, oscillatoryPhase_norm, one_mul]

theorem oscillatory_poleSquare_integral {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, oscillatoryPhase T u*poleSquare p u) =
      -((2*Real.pi*T : ℝ) : ℂ)*Complex.exp (I*p*T) := by
  have ha : (I*p).re < 0 := by simpa only [Complex.I_mul_re] using neg_neg_of_pos hp
  have he : (fun u => oscillatoryPhase T u*poleSquare p u) =
      fun u => -(oscillatoryPhase T u*squareKernel (I*p) u) := by
    funext u
    rw [squareKernel_pole, mul_neg, neg_neg]
  rw [he, integral_neg, squareKernel_angular_integral ha hT]
  ring

#print axioms oscillatory_poleSquare_integral

end Maxwell.Continuum.OscillatoryPole
