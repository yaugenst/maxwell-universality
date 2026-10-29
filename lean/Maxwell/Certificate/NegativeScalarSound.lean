import Maxwell.Certificate.NegativeScalarCore
import Maxwell.Certificate.GlobalScalarSound
import Maxwell.Spectral.BoxNegativeNeighborhood

namespace Maxwell.Certificate.NegativeScalar

open ScalarExpression GlobalScalar Maxwell.Spectral
open BoxNeighborhood BoxNegativeNeighborhood

noncomputable def Proposal.constants (p : Proposal) : Constants where
  half := fun _ => p.half
  P0 := 1023/1024
  s := p.s
  r := p.r
  rh := 0
  R := 0
  σ := 1/4096
  fn := fun _ => p.fn
  en := fun _ => p.en
  kn := fun _ j => p.kn j
  crossder := 0
  rhow := 0
  wn := p.wn
  wp2 := 0
  qfn := 0
  qw := 0
  rzero := 0

private theorem eval_lit (q : ℚ) : (lit q).eval = (q : ℝ) := rfl
private theorem eval_plus (a b : Expr) : (plus a b).eval = a.eval+b.eval := rfl
private theorem eval_minus (a b : Expr) : (minus a b).eval = a.eval-b.eval := rfl
private theorem eval_times (a b : Expr) : (times a b).eval = a.eval*b.eval := rfl
private theorem eval_divide (a b : Expr) : (divide a b).eval = a.eval/b.eval := by
  simp only [divide, Expr.eval, div_eq_mul_inv, one_mul]
private theorem eval_square (a : Expr) : (square a).eval = a.eval^2 := by
  simp only [square, Expr.eval, pow_two]

attribute [local simp] eval_lit eval_plus eval_minus eval_times eval_divide eval_square

theorem lossExpr_eval (p : Proposal) : (lossExpr p).eval = p.constants.negativeLoss := by
  simp [lossExpr, dotExpr, Constants.negativeLoss, Constants.dot,
    Proposal.constants, Fin.sum_univ_three]

theorem marginExpr_eval (p : Proposal) :
    (marginExpr p).eval = p.constants.P0-p.constants.negativeLoss := by
  simp [marginExpr, lossExpr_eval, Proposal.constants]

theorem smallExpr_eval (p : Proposal) :
    (smallExpr p).eval = p.constants.r-p.constants.s := by
  simp [smallExpr, Proposal.constants]

/-- Kernel acceptance supplies exactly the scalar hypotheses of the
negative-trial neighborhood theorem, at the original half-width `1/4096`. -/
theorem accepts_sound (p : Proposal) (e : Evidence) (h : accepts p e = true) :
    NegativeAccepted p.constants := by
  simp only [accepts, Bool.and_eq_true] at h
  obtain ⟨hgeom, hm, hs⟩ := h
  have hg : 0 ≤ p.half ∧ 0 ≤ p.s ∧
      piUpper/10*(sqrtThreeUpper*p.half) ≤ p.s := of_decide_eq_true hgeom
  have hm' := positiveCheck_sound _ _ hm
  have hs' := positiveCheck_sound _ _ hs
  rw [marginExpr_eval] at hm'
  rw [smallExpr_eval] at hs'
  exact ⟨fun _ => Rat.cast_nonneg.mpr hg.1, Rat.cast_nonneg.mpr hg.2.1,
    cube_radius_bound p.half p.s hg.1 hg.2.2, sub_pos.mp hs',
    by norm_num [Proposal.constants], by norm_num [Proposal.constants], sub_pos.mp hm'⟩

end Maxwell.Certificate.NegativeScalar
