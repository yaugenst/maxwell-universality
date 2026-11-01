import Maxwell.Continuum.RationalDataflowExpression
import Maxwell.Continuum.RationalDataflowBankWidth

/-! Literal storage bounds and fixed three-term sums for compiled rational
expressions. These depend only on the expression syntax. -/
namespace Maxwell.Continuum.RationalDataflow.PolynomialExpression

def literalBound : PolynomialExpression→ℕ
  | .literal q => (Parts.literal q).bitWidth
  | .inputRegister _ => 0
  | .binary _ x y => max x.literalBound y.literalBound

theorem literalsFit_bound (e : PolynomialExpression) (B : ℕ) (h:e.literalBound≤B) : e.LiteralsFit B := by
  induction e with
  | literal q => exact (Parts.width_bitWidth _).mono h
  | inputRegister => trivial
  | binary op x y hx hy => exact ⟨hx ((le_max_left _ _).trans h),hy ((le_max_right _ _).trans h)⟩

def sum3 (f : Fin 3→PolynomialExpression) : PolynomialExpression :=
  .binary .add (f 0) (.binary .add (f 1) (f 2))

theorem evaluate_sum3 (f : Fin 3→PolynomialExpression) (v : ℕ→ℚ) :
    (sum3 f).evaluate v=∑j,(f j).evaluate v := by
  simp [sum3,evaluate,binaryValue,Fin.sum_univ_succ]

theorem scoped_sum3 (f : Fin 3→PolynomialExpression) (base : ℕ) (h:∀j,(f j).Scoped base) :
    (sum3 f).Scoped base := ⟨h 0,h 1,h 2⟩

#print axioms literalsFit_bound
end Maxwell.Continuum.RationalDataflow.PolynomialExpression
