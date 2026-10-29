import Maxwell.Certificate.GlobalScalar

namespace Maxwell.Certificate.GlobalScalar

open Maxwell.Spectral Maxwell.Spectral.BoxNeighborhood ScalarExpression

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
    (dotExpr p v).eval = p.constants.dot (fun j => (v j : ℝ)) := by
  simp [dotExpr, Constants.dot, Proposal.constants, Fin.sum_univ_three]

theorem negativeLossExpr_eval (p : Proposal) :
    (negativeLossExpr p).eval = p.constants.negativeLoss := by
  simp [negativeLossExpr, dotExpr_eval, Constants.negativeLoss, Proposal.constants]

theorem positiveLossExpr_eval (p : Proposal) :
    (positiveLossExpr p).eval = p.constants.positiveLoss := by
  simp [positiveLossExpr, dotExpr_eval, Constants.positiveLoss, Proposal.constants]

theorem gradientLossExpr_eval (p : Proposal) :
    (gradientLossExpr p).eval = p.constants.gradientLoss := by
  simp [gradientLossExpr, Constants.gradientLoss, Proposal.constants]

theorem crossCoefficientExpr_eval (p : Proposal) :
    (crossCoefficientExpr p).eval = BoxMixedForm.projectionCrossCoefficient
      p.constants.s p.constants.r p.constants.R := by
  simp [crossCoefficientExpr, BoxMixedForm.projectionCrossCoefficient, Proposal.constants]

theorem crossExpr_eval (p : Proposal) :
    (crossExpr p).eval = p.constants.cross := by
  simp [crossExpr, dotExpr_eval, crossCoefficientExpr_eval, Constants.cross, Proposal.constants]

theorem baseExpr_eval (p : Proposal) : (baseExpr p).eval = p.constants.base := by
  simp [baseExpr, Constants.base, Proposal.constants]

theorem shiftExpr_eval (p : Proposal) : (shiftExpr p).eval = p.constants.shift := by
  simp [shiftExpr, Constants.shift, Proposal.constants]

theorem wmaxExpr_eval (p : Proposal) : (wmaxExpr p).eval = p.constants.wmax := by
  simp [wmaxExpr, Expr.eval, baseExpr_eval, Constants.wmax]

theorem curlmaxExpr_eval (p : Proposal) : (curlmaxExpr p).eval = p.constants.curlmax := by
  simp [curlmaxExpr, Expr.eval, baseExpr_eval, Constants.curlmax, Proposal.constants]

theorem chiExpr_eval (p : Proposal) : (chiExpr p).eval = p.constants.chi := by
  simp [chiExpr, Expr.eval, baseExpr_eval, shiftExpr_eval, Constants.chi]

theorem projectorCoefficientExpr_eval (p : Proposal) :
    (projectorCoefficientExpr p).eval =
      (p.constants.rh/2+3+p.constants.s/p.constants.rh)/(p.constants.rh-p.constants.s)^2 := by
  simp [projectorCoefficientExpr, Proposal.constants]

theorem positiveResidualExpr_eval (p : Proposal) :
    (positiveResidualExpr p).eval = p.constants.positiveResidual := by
  simp [positiveResidualExpr, chiExpr_eval, wmaxExpr_eval, curlmaxExpr_eval,
    dotExpr_eval, projectorCoefficientExpr_eval, Constants.positiveResidual, Proposal.constants]

theorem gradientResidualExpr_eval (p : Proposal) :
    (gradientResidualExpr p).eval = p.constants.gradientResidual := by
  simp [gradientResidualExpr, chiExpr_eval, wmaxExpr_eval, curlmaxExpr_eval,
    dotExpr_eval, Constants.gradientResidual, Proposal.constants]

theorem positiveEtaExpr_eval (p : Proposal) :
    (positiveEtaExpr p).eval = p.constants.positiveEta := by
  simp [positiveEtaExpr, positiveResidualExpr_eval, Constants.positiveEta, Proposal.constants]

theorem gradientEtaExpr_eval (p : Proposal) :
    (gradientEtaExpr p).eval = p.constants.gradientEta := by
  simp [gradientEtaExpr, gradientResidualExpr_eval, Constants.gradientEta]

theorem negativeExpr_eval (p : Proposal) :
    (negativeExpr p).eval = p.constants.P0-p.constants.negativeLoss := by
  simp [negativeExpr, negativeLossExpr_eval, Proposal.constants]

theorem positiveExpr_eval (p : Proposal) :
    (positiveExpr p).eval = p.constants.P0-p.constants.positiveLoss-p.constants.positiveEta := by
  simp [positiveExpr, positiveLossExpr_eval, positiveEtaExpr_eval, Proposal.constants]

theorem gradientExpr_eval (p : Proposal) :
    (gradientExpr p).eval = 1-p.constants.gradientLoss-p.constants.gradientEta := by
  simp [gradientExpr, gradientLossExpr_eval, gradientEtaExpr_eval]

theorem determinantExpr_eval (p : Proposal) :
    (determinantExpr p).eval =
      (p.constants.P0-p.constants.positiveLoss-p.constants.positiveEta)*
        (1-p.constants.gradientLoss-p.constants.gradientEta)-
      (p.constants.cross+Real.sqrt (p.constants.positiveEta*p.constants.gradientEta))^2 := by
  simp [determinantExpr, positiveExpr_eval, gradientExpr_eval, crossExpr_eval,
    positiveEtaExpr_eval, gradientEtaExpr_eval, Expr.eval]

theorem smallLowExpr_eval (p : Proposal) :
    (smallLowExpr p).eval = p.constants.r-p.constants.s := by
  simp [smallLowExpr, Proposal.constants]

theorem smallHighExpr_eval (p : Proposal) :
    (smallHighExpr p).eval = p.constants.rh-p.constants.s := by
  simp [smallHighExpr, Proposal.constants]

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
    (p.cutoff : ℝ) ≤ p.constants.R^2 := by
  change (p.cutoff : ℝ) ≤ (p.R : ℝ)^2
  exact_mod_cast accepts_cutoff_le p c h

/-- Every finite accepted record yields exactly the inequalities required
by the actual whole-box spectral theorem. -/
theorem accepts_sound (p : Proposal) (c : Evidence) (h : accepts p c = true) :
    Accepted p.constants := by
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
  exact ⟨fun _ => Rat.cast_nonneg.mpr hq.1, Rat.cast_nonneg.mpr hq.2.1,
    cube_radius_bound p.half p.s hq.1 hq.2.2.2.1,
    sub_pos.mp hl', sub_pos.mp hh', Rat.cast_nonneg.mpr hq.2.2.1,
    by norm_num [Proposal.constants], by norm_num [Proposal.constants],
    hb', hs', hn', hp', hg', sub_pos.mp hd'⟩

end Maxwell.Certificate.GlobalScalar
