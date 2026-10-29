import Maxwell.Certificate.UniformLocalScalarCore
import Maxwell.Certificate.GlobalScalar
import Maxwell.Spectral.BoxNeighborhoodGeneral

namespace Maxwell.Certificate.UniformLocalScalar
open Maxwell.Spectral Maxwell.Spectral.BoxNeighborhoodGeneral ScalarExpression
open GlobalScalar (piUpper sqrtThreeUpper geometryCheck lit plus minus times divide square
  dotExpr smallLowExpr smallHighExpr positiveCheck)
noncomputable section

def constants (p : Proposal) : Constants where
  rho := 14
  half := fun _ => p.half
  P0 := 1023/1024
  s := p.s
  r := p.r
  rh := p.rh
  R := p.R
  σ := 1/4096
  fn := fun i => p.fn i
  en := fun i => p.en i
  kn := fun i j => p.kn i j
  crossder := fun j => p.crossder j
  rhow := fun i j => p.rhow i j
  wn := p.wn
  wp2 := p.wp2
  qfn := p.qfn
  qw := p.qw
  rzero := p.rzero

private theorem eval_lit (q : ℚ) : (lit q).eval = (q : ℝ) := rfl
private theorem eval_plus (a b : Expr) : (plus a b).eval = a.eval + b.eval := rfl
private theorem eval_minus (a b : Expr) : (minus a b).eval = a.eval - b.eval := rfl
private theorem eval_times (a b : Expr) : (times a b).eval = a.eval * b.eval := rfl
private theorem eval_divide (a b : Expr) : (divide a b).eval = a.eval / b.eval := by
  simp only [divide, Expr.eval, div_eq_mul_inv, one_mul]
private theorem eval_square (a : Expr) : (square a).eval = a.eval^2 := by
  simp only [square, Expr.eval, pow_two]

attribute [local simp] eval_lit eval_plus eval_minus eval_times eval_divide eval_square

theorem dotExpr_eval (p : Proposal) (v : Fin 3 → ℚ) :
    (dotExpr p v).eval = (constants p).dot (fun j => (v j : ℝ)) := by
  simp [dotExpr, Constants.dot, constants, Fin.sum_univ_three]

theorem negativeLossExpr_eval (p : Proposal) :
    (negativeLossExpr p).eval = (constants p).negativeLoss := by
  simp [negativeLossExpr, dotExpr_eval, Constants.negativeLoss, constants]

theorem positiveLossExpr_eval (p : Proposal) :
    (positiveLossExpr p).eval = (constants p).positiveLoss := by
  simp [positiveLossExpr, dotExpr_eval, Constants.positiveLoss, constants]

theorem gradientLossExpr_eval (p : Proposal) :
    (gradientLossExpr p).eval = (constants p).gradientLoss := by
  simp [gradientLossExpr, Constants.gradientLoss, constants]

theorem crossCoefficientExpr_eval (p : Proposal) :
    (crossCoefficientExpr p).eval = BoxMixedForm.projectionCrossCoefficient
      (constants p).s (constants p).r (constants p).R := by
  simp [crossCoefficientExpr, BoxMixedForm.projectionCrossCoefficient, constants]

theorem crossExpr_eval (p : Proposal) :
    (crossExpr p).eval = (constants p).cross := by
  simp [crossExpr, dotExpr_eval, crossCoefficientExpr_eval, Constants.cross, constants]

theorem baseExpr_eval (p : Proposal) : (baseExpr p).eval = (constants p).base := by
  simp [baseExpr, Constants.base, constants]

theorem shiftExpr_eval (p : Proposal) : (shiftExpr p).eval = (constants p).shift := by
  simp [shiftExpr, Constants.shift, constants]

theorem wmaxExpr_eval (p : Proposal) : (wmaxExpr p).eval = (constants p).wmax := by
  simp [wmaxExpr, Expr.eval, baseExpr_eval, Constants.wmax]

theorem curlmaxExpr_eval (p : Proposal) : (curlmaxExpr p).eval = (constants p).curlmax := by
  simp [curlmaxExpr, Expr.eval, baseExpr_eval, Constants.curlmax, constants]

theorem chiExpr_eval (p : Proposal) : (chiExpr p).eval = (constants p).chi := by
  simp [chiExpr, Expr.eval, baseExpr_eval, shiftExpr_eval, Constants.chi]

theorem projectorCoefficientExpr_eval (p : Proposal) :
    (projectorCoefficientExpr p).eval =
      ((constants p).rh/2+3+(constants p).s/(constants p).rh)/((constants p).rh-(constants p).s)^2 := by
  simp [projectorCoefficientExpr, constants]

theorem positiveResidualExpr_eval (p : Proposal) :
    (positiveResidualExpr p).eval = (constants p).positiveResidual := by
  simp [positiveResidualExpr, chiExpr_eval, wmaxExpr_eval, curlmaxExpr_eval,
    dotExpr_eval, projectorCoefficientExpr_eval, Constants.positiveResidual, constants]

theorem gradientResidualExpr_eval (p : Proposal) :
    (gradientResidualExpr p).eval = (constants p).gradientResidual := by
  simp [gradientResidualExpr, chiExpr_eval, wmaxExpr_eval, curlmaxExpr_eval,
    dotExpr_eval, Constants.gradientResidual, constants]

theorem positiveEtaExpr_eval (p : Proposal) :
    (positiveEtaExpr p).eval = (constants p).positiveEta := by
  simp [positiveEtaExpr, positiveResidualExpr_eval, Constants.positiveEta, constants]

theorem gradientEtaExpr_eval (p : Proposal) :
    (gradientEtaExpr p).eval = (constants p).gradientEta := by
  simp [gradientEtaExpr, gradientResidualExpr_eval, Constants.gradientEta]

theorem negativeExpr_eval (p : Proposal) :
    (negativeExpr p).eval = (constants p).P0-(constants p).negativeLoss := by
  simp [negativeExpr, negativeLossExpr_eval, constants]

theorem positiveExpr_eval (p : Proposal) :
    (positiveExpr p).eval = (constants p).P0-(constants p).positiveLoss-(constants p).positiveEta := by
  simp [positiveExpr, positiveLossExpr_eval, positiveEtaExpr_eval, constants]

theorem gradientExpr_eval (p : Proposal) :
    (gradientExpr p).eval = 1-(constants p).gradientLoss-(constants p).gradientEta := by
  simp [gradientExpr, gradientLossExpr_eval, gradientEtaExpr_eval]

theorem determinantExpr_eval (p : Proposal) :
    (determinantExpr p).eval =
      ((constants p).P0-(constants p).positiveLoss-(constants p).positiveEta)*
        (1-(constants p).gradientLoss-(constants p).gradientEta)-
      ((constants p).cross+Real.sqrt ((constants p).positiveEta*(constants p).gradientEta))^2 := by
  simp [determinantExpr, positiveExpr_eval, gradientExpr_eval, crossExpr_eval,
    positiveEtaExpr_eval, gradientEtaExpr_eval, Expr.eval]

theorem smallLowExpr_eval (p : Proposal) :
    (smallLowExpr p).eval = (constants p).r-(constants p).s := by
  simp [smallLowExpr, constants]

theorem smallHighExpr_eval (p : Proposal) :
    (smallHighExpr p).eval = (constants p).rh-(constants p).s := by
  simp [smallHighExpr, constants]

theorem positiveCheck_sound (e : Expr) (c : ScalarExpression.Certificate)
    (h : positiveCheck e c = true) : 0 < e.eval := by
  simp only [positiveCheck, Bool.and_eq_true] at h
  simpa only [Rat.cast_zero] using
    Interval.lowerCheck_sound h.2 (verifyExpr_sound e c h.1)

theorem geometryCheck_cutoff_le (p : Proposal) (h : geometryCheck p = true) :
    p.cutoff ≤ p.R^2 := by
  exact (of_decide_eq_true h : 0 ≤ p.half ∧ 0 ≤ p.s ∧ 0 ≤ p.R ∧
    piUpper/10*(sqrtThreeUpper*p.half) ≤ p.s ∧ p.cutoff ≤ p.R^2).2.2.2.2

theorem accepts_cutoff_le (p : Proposal) (c : Evidence) (h : accepts p c = true) :
    p.cutoff ≤ p.R^2 := by
  simp only [accepts, Bool.and_eq_true] at h
  exact geometryCheck_cutoff_le p h.1

theorem accepts_cutoff_le_real (p : Proposal) (c : Evidence) (h : accepts p c = true) :
    (p.cutoff : ℝ) ≤ (constants p).R^2 := by
  change (p.cutoff : ℝ) ≤ (p.R : ℝ)^2
  exact_mod_cast accepts_cutoff_le p c h

/-- Every finite accepted record yields exactly the inequalities required
by the actual whole-box spectral theorem. -/
theorem accepts_sound (p : Proposal) (c : Evidence) (h : accepts p c = true) :
    Accepted (constants p) := by
  simp only [accepts, Bool.and_eq_true] at h
  obtain ⟨hgeom, hn, hp, hg, hd, hl, hh, hb, hs⟩ := h
  have hq : 0 ≤ p.half ∧ 0 ≤ p.s ∧ 0 ≤ p.R ∧
      piUpper/10*(sqrtThreeUpper*p.half) ≤ p.s ∧ p.cutoff ≤ p.R^2 := of_decide_eq_true hgeom
  have hn' := positiveCheck_sound _ _ hn
  have hp' := positiveCheck_sound _ _ hp
  have hg' := positiveCheck_sound _ _ hg
  have hd' := positiveCheck_sound _ _ hd
  have hl' := positiveCheck_sound _ _ hl
  have hh' := positiveCheck_sound _ _ hh
  have hb' := positiveCheck_sound _ _ hb
  have hs' := positiveCheck_sound _ _ hs
  rw [negativeExpr_eval] at hn'
  rw [positiveExpr_eval] at hp'
  rw [gradientExpr_eval] at hg'
  rw [determinantExpr_eval] at hd'
  rw [smallLowExpr_eval] at hl'
  rw [smallHighExpr_eval] at hh'
  rw [baseExpr_eval] at hb'
  rw [shiftExpr_eval] at hs'
  exact ⟨by norm_num [constants], fun _ => Rat.cast_nonneg.mpr hq.1, Rat.cast_nonneg.mpr hq.2.1,
    GlobalScalar.cube_radius_bound p.half p.s hq.1 hq.2.2.2.1,
    sub_pos.mp hl', sub_pos.mp hh', Rat.cast_nonneg.mpr hq.2.2.1,
    by norm_num [constants], by norm_num [constants],
    hb', hs', hn', hp', hg', sub_pos.mp hd'⟩

end
end Maxwell.Certificate.UniformLocalScalar
