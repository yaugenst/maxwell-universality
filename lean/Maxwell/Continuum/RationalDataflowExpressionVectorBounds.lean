import Maxwell.Continuum.RationalDataflowExpressionVector

/-! A fixed expression-vector program has linear word growth and quadratic
running time in its input word width. Its syntax determines the constants. -/
namespace Maxwell.Continuum.RationalDataflow.ExpressionVector
open PolynomialExpression
set_option maxHeartbeats 1800000

variable {n : ℕ}

def widthCoefficient (e : Fin n→PolynomialExpression) : List (Fin n)→ℕ
  | [] => 1
  | r::rest => widthCoefficient e rest*(2^(3*(e r).nodes)+1)
def costCoefficient (e : Fin n→PolynomialExpression) : List (Fin n)→ℕ
  | [] => 1
  | r::rest => ((3*(e r).nodes+1)*2^100+1+costCoefficient e rest)*(2^(3*(e r).nodes)+3)^2

theorem resultWidth_linear (e : Fin n→PolynomialExpression) (rows : List (Fin n)) (B : ℕ) :
    resultWidth e rows B+1≤widthCoefficient e rows*(B+1) := by
  induction rows generalizing B with
  | nil => simp [resultWidth,widthCoefficient]
  | cons r rest ih =>
    have bound : (e r).width B+1≤(2^(3*(e r).nodes)+1)*(B+1) := by
      unfold PolynomialExpression.width
      nlinarith
    exact (ih ((e r).width B)).trans ((Nat.mul_le_mul_left (widthCoefficient e rest) bound).trans_eq (by
      simp only [widthCoefficient,Nat.mul_assoc]))

theorem rowCost_quadratic (e : PolynomialExpression) (B : ℕ) :
    rowCost e B≤((3*e.nodes+1)*2^100+1)*(e.width B+3)^2 := by
  have square : 1≤(e.width B+3)^2 := one_le_pow₀ (by omega)
  have smaller : 2^96*(e.width B+2)^2≤2^100*(e.width B+3)^2 :=
    Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
  unfold rowCost PolynomialExpression.cost operationCost stageCost
  nlinarith only [square,smaller]

theorem cost_quadratic (e : Fin n→PolynomialExpression) (rows : List (Fin n)) (B : ℕ) :
    cost e rows B≤costCoefficient e rows*(B+3)^2 := by
  induction rows generalizing B with
  | nil => simp only [cost,costCoefficient,Nat.one_mul];exact one_le_pow₀ (by omega)
  | cons r rest ih =>
    have grow : (e r).width B+3≤(2^(3*(e r).nodes)+3)*(B+3) := by
      unfold PolynomialExpression.width
      calc
        _≤2^(3*(e r).nodes)*(B+3)+3*(B+3) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _=_ := by ring
    have pair:=Nat.add_le_add (rowCost_quadratic (e r) B) (ih ((e r).width B))
    calc
      cost e (r::rest) B≤((3*(e r).nodes+1)*2^100+1+costCoefficient e rest)*((e r).width B+3)^2 := by
        simpa only [Nat.add_mul,cost] using pair
      _≤((3*(e r).nodes+1)*2^100+1+costCoefficient e rest)*
          ((2^(3*(e r).nodes)+3)*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left grow 2)
      _=costCoefficient e (r::rest)*(B+3)^2 := by simp only [costCoefficient,mul_pow,Nat.mul_assoc]

#print axioms cost_quadratic
end Maxwell.Continuum.RationalDataflow.ExpressionVector
