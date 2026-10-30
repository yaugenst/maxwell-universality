import Maxwell.Continuum.ParameterBinaryBounds
import Maxwell.Continuum.ParameterBox

/-! Derived binary exponent bounds for the literal global and detuning
budgets. These are arithmetic consequences of the input bounds. -/

namespace Maxwell.Continuum.Parameters

set_option maxRecDepth 4096

def globalExponent (e j m n k p l : ℕ) : ℕ :=
  32*e+2*(n+1)+2*(j+m+2)+4*(k+1)+2*(p+1)+100*l

theorem globalBudget_binary {e J m N L d j u n k p l : ℕ} {K : ℚ}
    (hJ : (J : ℚ) ≤ (2 : ℚ)^j) (hm : (m : ℚ) ≤ (2 : ℚ)^u)
    (hN : (N : ℚ) ≤ (2 : ℚ)^n) (hL : (L : ℚ) ≤ (2 : ℚ)^l)
    (hK0 : 0 ≤ K) (hK : K ≤ (2 : ℚ)^k) (ha : (alpha L d)⁻¹ ≤ (2 : ℚ)^p) :
    globalBudget e J m N L d K ≤ (2 : ℚ)^globalExponent e j u n k p l := by
  have hC : ((2 : ℚ)^e)^32 ≤ (2 : ℚ)^(32*e) := by rw [← pow_mul, Nat.mul_comm]
  have hN' := binary_pow (by positivity : (0 : ℚ) ≤ 1+(N : ℚ)) (binary_one_add hN) 2
  have hJ' := binary_pow (by positivity : (0 : ℚ) ≤ 1+(J : ℚ)+m)
    (binary_add (binary_one_add hJ) hm) 2
  have hK' := binary_pow (by positivity : (0 : ℚ) ≤ 1+K) (binary_one_add hK) 4
  have hα0 : 0 ≤ alpha L d := by unfold alpha; positivity
  have ha' := binary_pow (by positivity : (0 : ℚ) ≤ 1+(alpha L d)⁻¹) (binary_one_add ha) 2
  have hL' := binary_pow (Nat.cast_nonneg L) hL 100
  have hprod := binary_mul (binary_mul (binary_mul (binary_mul
    (binary_mul hC hN' (by positivity)) hJ' (by positivity)) hK' (by positivity))
      ha' (by positivity)) hL' (by positivity)
  convert hprod using 1
  · rfl
  · congr 1
    unfold globalExponent
    omega

theorem stoppingRatio_product (e J m N L d : ℕ) (K ε τ : ℚ) :
    stoppingRatio e J m N L d K ε τ =
      (2 : ℚ)^35*(m : ℚ)*N*globalBudget e J m N L d K*τ⁻¹*ε⁻¹ := by
  unfold stoppingRatio errorBudget inverseBudget
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

def stoppingExponent (e j m n k p l t r : ℕ) : ℕ :=
  35+m+n+globalExponent e j m n k p l+t+r

theorem stoppingRatio_binary {e J m N L d j u n k p l t r : ℕ} {K ε τ : ℚ}
    (hJ : (J : ℚ) ≤ (2 : ℚ)^j) (hm : (m : ℚ) ≤ (2 : ℚ)^u)
    (hN : (N : ℚ) ≤ (2 : ℚ)^n) (hL : (L : ℚ) ≤ (2 : ℚ)^l)
    (hK0 : 0 ≤ K) (hK : K ≤ (2 : ℚ)^k) (ha : (alpha L d)⁻¹ ≤ (2 : ℚ)^p)
    (hε : 0 < ε) (hεb : ε⁻¹ ≤ (2 : ℚ)^r) (hτ : 0 < τ) (hτb : τ⁻¹ ≤ (2 : ℚ)^t) :
    stoppingRatio e J m N L d K ε τ ≤ (2 : ℚ)^stoppingExponent e j u n k p l t r := by
  have hglobal := globalBudget_binary (e := e) hJ hm hN hL hK0 hK ha
  have hprod := binary_mul (binary_mul (binary_mul
    (binary_mul (binary_mul (le_refl ((2 : ℚ)^35)) hm (Nat.cast_nonneg m))
      hN (Nat.cast_nonneg N)) hglobal (globalBudget_nonneg _ _ _ _ _ _ _))
        hτb (inv_pos.mpr hτ).le) hεb (inv_pos.mpr hε).le
  rw [stoppingRatio_product]
  exact hprod

/-- An integer form of the input-size parameter, with no evaluated real log. -/
def inputLog (m : ℕ) : ℕ := 1+Nat.clog 2 (m+2)

theorem inputLog_pos (m : ℕ) : 0 < inputLog m := by unfold inputLog; omega

theorem input_le_binary (m : ℕ) : m ≤ 2^inputLog m :=
  (Nat.le_add_right m 2).trans ((Nat.le_pow_clog (by decide) (m+2)).trans
    (Nat.pow_le_pow_right (by decide) (by unfold inputLog; omega)))

#print axioms globalBudget_binary
#print axioms stoppingRatio_binary

end Maxwell.Continuum.Parameters
