import Maxwell.Continuum.DefinitenessExpressions

/-! Circuit size bounds depend on matrix dimension and entry size, without
expanding the generated Schur expressions. -/
namespace Maxwell.Continuum.Calibration.ExpressionDefiniteness
set_option maxHeartbeats 1000000

theorem schur_nodes {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) RationalExpression)
    (C : ℕ) (h : ∀i j,(A i j).nodes≤ C) : ∀i j,(schur A i j).nodes≤4*C+4 := by
  intro i j
  simp only [schur,RationalExpression.nodes]
  have h₁:=h i.succ j.succ
  have h₂:=h i.succ 0
  have h₃:=h 0 j.succ
  have h₄:=h 0 0
  omega

theorem extent_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (C : ℕ) (h : ∀i j,(A i j).nodes≤ C) : extent A≤(C+2)*5^n := by
  induction n generalizing C with
  | zero => simp only [extent,pow_zero,mul_one];omega
  | succ n ih =>
    simp only [extent,max_le_iff]
    have power : 1≤5^(n+1) := Nat.one_le_pow _ _ (by decide)
    refine ⟨(h 0 0).trans ?_,?_⟩
    · nlinarith only [Nat.mul_le_mul_left (C+2) power]
    · have bound:=ih (schur A) (4*C+4) (schur_nodes A C h)
      apply bound.trans
      rw [pow_succ]
      nlinarith only [Nat.zero_le (5^n)]

#print axioms extent_bound
end Maxwell.Continuum.Calibration.ExpressionDefiniteness
