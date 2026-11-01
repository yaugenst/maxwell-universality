import Maxwell.Continuum.ParameterOuterCost
import Maxwell.Continuum.ParameterOuterInitializeBounds

/-! Polynomial cost for the complete executed parameter search. Raw stored
operand widths are charged directly, and the continuum binary budget controls
every candidate visited before the first success. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
attribute [local irreducible] OuterInitial.setup initialWidthCoefficient costCoefficient
  widthResourceCoefficient

theorem source_width_bound (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length ≤ B) :
    sourceWidth (dataOf v) ≤ 10*B := by
  have sub : Finset.Icc 2200 2260⊆ids := by
    intro i hi
    simp only [ids,Compare.ids,extra,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hi)))))
  have h0 := hw 2210 (sub (by simp only [Finset.mem_Icc];omega))
  have h1 := hw 2211 (sub (by simp only [Finset.mem_Icc];omega))
  have h2 := hw 2212 (sub (by simp only [Finset.mem_Icc];omega))
  have h3 := hw 2213 (sub (by simp only [Finset.mem_Icc];omega))
  have h4 := hw 2214 (sub (by simp only [Finset.mem_Icc];omega))
  have h5 := hw 2215 (sub (by simp only [Finset.mem_Icc];omega))
  have h6 := hw 2216 (sub (by simp only [Finset.mem_Icc];omega))
  have h7 := hw 2217 (sub (by simp only [Finset.mem_Icc];omega))
  have h8 := hw 2218 (sub (by simp only [Finset.mem_Icc];omega))
  have h9 := hw 2219 (sub (by simp only [Finset.mem_Icc];omega))
  change (v 2210).bits.length+(v 2211).bits.length+(v 2212).bits.length+
    (v 2213).bits.length+(v 2214).bits.length+(v 2215).bits.length+(v 2216).bits.length+
    (v 2217).bits.length+(v 2218).bits.length+(v 2219).bits.length ≤ _
  omega


#print axioms source_width_bound

def resultWidthCoefficient (M : ℕ) : ℕ := initialWidthCoefficient*(17*M+1)^2+widthResourceCoefficient M*10^12
def polynomialCoefficient (M : ℕ) : ℕ := costCoefficient*(resultWidthCoefficient M+1033)^5
attribute [local irreducible] resultWidthCoefficient polynomialCoefficient

theorem result_width_polynomial (v : ℕ→ℕ) (hD : (dataOf v).Positive) (M e p B : ℕ) (hℓ : 0<v 2200)
    (hI : ((dataOf v).input hD).BinaryBudget p (v 2200)) (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M)
    (hb : v 2201 ≤ M) (hw : ∀i∈ids,(v i).bits.length ≤ B) :
    resultWidth v hD e B hℓ ≤ resultWidthCoefficient M*(B+v 2200+1)^12 := by
  let X := B+v 2200+1
  have hX : 1 ≤ X := by unfold X;omega
  have hN : initialExponent (v 2201) (v 2200) ≤ 17*M*(v 2200) :=
    (initialExponent_le_candidate hb).trans (candidate_exponent_le (by omega) hℓ)
  have hraw := source_width_bound v B hw
  have hi := initial_width_bound v B
  have hmeasure : B+initialExponent (v 2201) (v 2200)+1 ≤ (17*M+1)*X := by
    have hm : B+1 ≤ (17*M+1)*(B+1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold X;nlinarith only [hN,hm,Nat.zero_le (v 2200)]
  have hi' : initialWidth v B ≤ (initialWidthCoefficient*(17*M+1)^2)*X^12 := by
    calc
      _ ≤ initialWidthCoefficient*((17*M+1)*X)^2 := hi.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmeasure 2))
      _ = (initialWidthCoefficient*(17*M+1)^2)*X^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by decide))
  have hsource : sourceWidth (dataOf v)+v 2200+1 ≤ 10*X := by unfold X;omega
  have hw' := loop_width_polynomial (dataOf v) hD M e p (v 2201) (v 2200) (initialWidth v B)
    hI hM he hp hb hℓ
  change resultWidth v hD e B hℓ ≤ _ at hw'
  have hg : widthResourceCoefficient M*(sourceWidth (dataOf v)+v 2200+1)^12 ≤
      (widthResourceCoefficient M*10^12)*X^12 := by
    calc
      _ ≤ widthResourceCoefficient M*(10*X)^12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsource 12)
      _ = _ := by ring
  change resultWidth v hD e B hℓ ≤ resultWidthCoefficient M*X^12
  unfold resultWidthCoefficient
  nlinarith only [hw',hi',hg]


#print axioms result_width_polynomial

theorem polynomial_cost (v : ℕ→ℕ) (hD : (dataOf v).Positive) (M e p B : ℕ) (hℓ : 0<v 2200)
    (hI : ((dataOf v).input hD).BinaryBudget p (v 2200)) (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M)
    (hb : v 2201 ≤ M) (hw : ∀i∈ids,(v i).bits.length ≤ B) :
    costBound v hD e B hℓ ≤ polynomialCoefficient M*(B+v 2200+1)^60 := by
  let X := B+v 2200+1
  have hX : 1 ≤ X := by unfold X;omega
  have h1 := Nat.one_le_pow 12 X hX
  have hw' := result_width_polynomial v hD M e p B hℓ hI hM he hp hb hw
  change resultWidth v hD e B hℓ ≤ resultWidthCoefficient M*X^12 at hw'
  have hsum : resultWidth v hD e B hℓ+1033 ≤ (resultWidthCoefficient M+1033)*X^12 := by
    nlinarith only [hw',h1]
  calc
    _ ≤ costCoefficient*(resultWidth v hD e B hℓ+1033)^5 := cost_bound v hD e B hℓ
    _ ≤ costCoefficient*((resultWidthCoefficient M+1033)*X^12)^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 5)
    _ = _ := by
      change _=polynomialCoefficient M*X^60
      unfold polynomialCoefficient
      rw [mul_pow, ←pow_mul, ←Nat.mul_assoc]

#print axioms polynomial_cost
end Maxwell.Continuum.Parameters.OuterMachine
