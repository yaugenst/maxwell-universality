import Maxwell.Continuum.ParameterOuterWidthBound

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def scaleCoefficient (M : ℕ) : ℕ := 2^(6+45*M)+2^(11*M)+17*M

theorem visited_scales (D : Data) (hD : D.Positive) (M e p base ℓ : ℕ)
    (hI : (D.input hD).BinaryBudget p ℓ) (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M)
    (hb : base ≤ M) (hℓ : 0<ℓ) (n : ℕ) (hn : n ≤ selectedOuterSteps (D.input hD) e base ℓ hℓ) :
    let k := initialExponent base ℓ+n
    let K := scaleCoefficient M*ℓ^6
    k ≤ K ∧ stageSpacing (D.input hD) e k ≤ K ∧ stageBuffer (D.input hD) e k ≤ K ∧ stageLength k ≤ K := by
  dsimp only
  have hs := selected_scales hI hM he hp hb hℓ
  have hc := selectedOuter_le_candidate hI hM he hp hb hℓ
  have hk : initialExponent base ℓ+n ≤ selectedOuterExponent (D.input hD) e base ℓ hℓ := by
    unfold selectedOuterExponent;omega
  have hkc := hk.trans hc
  have hlen : ℓ ≤ ℓ^6 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ ℓ) (by decide : 1 ≤ 6)
  have h1 : 17*M ≤ scaleCoefficient M := Nat.le_add_left _ _
  have h2 : 2^(11*M) ≤ scaleCoefficient M := by
    unfold scaleCoefficient
    exact Nat.le_add_right_of_le (Nat.le_add_left _ _)
  have h3 : 2^(6+45*M) ≤ scaleCoefficient M := Nat.le_add_right_of_le (Nat.le_add_right _ _)
  refine ⟨?_,?_,?_,?_⟩
  · exact (hkc.trans (candidate_exponent_le (by omega) hℓ)).trans (Nat.mul_le_mul h1 hlen)
  · have hd := spacing_before_candidate hI hM he hp hℓ hkc
    exact hd.trans (Nat.mul_le_mul ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 9*M ≤ 11*M)).trans h2) hlen)
  · exact (buffer_before_candidate hI hM he hp hℓ hkc).trans (Nat.mul_le_mul h2 hlen)
  · exact ((Nat.pow_le_pow_right (by decide : 1 ≤ 8) hk).trans hs.1).trans (Nat.mul_le_mul_right _ h3)

def widthResourceCoefficient (M : ℕ) : ℕ := (scaleCoefficient M+1)*stageWidthCoefficient*(scaleCoefficient M+2)

theorem loop_width_polynomial (D : Data) (hD : D.Positive) (M e p base ℓ B : ℕ)
    (hI : (D.input hD).BinaryBudget p ℓ) (hM : 4096 ≤ M) (he : e ≤ M) (hp : p ≤ M)
    (hb : base ≤ M) (hℓ : 0<ℓ) :
    loopWidth D hD e base ℓ B hℓ ≤ B+widthResourceCoefficient M*(sourceWidth D+ℓ+1)^12 := by
  let X := sourceWidth D+ℓ+1
  let K := scaleCoefficient M*ℓ^6
  have hX : 1 ≤ X := by unfold X;omega
  have hX6 : X ≤ X^6 := by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 6)
  have h16 : 1 ≤ X^6 := Nat.one_le_pow _ _ hX
  have hL : ℓ ≤ X := by unfold X;omega
  have hK : K ≤ scaleCoefficient M*X^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 6)
  have hK1 : K+1 ≤ (scaleCoefficient M+1)*X^6 := by nlinarith only [hK,h16]
  have hraw : sourceWidth D ≤ X^6 := (show sourceWidth D ≤ X by unfold X;omega).trans hX6
  have hsum : sourceWidth D+K+1 ≤ (scaleCoefficient M+2)*X^6 := by nlinarith only [hraw,hK,h16]
  have hw := loop_width_bound D hD e base ℓ B K hℓ (visited_scales D hD M e p base ℓ hI hM he hp hb hℓ)
  calc
    _ ≤ B+(K+1)*stageWidthCoefficient*(sourceWidth D+K+1) := hw
    _ ≤ B+((scaleCoefficient M+1)*X^6)*stageWidthCoefficient*((scaleCoefficient M+2)*X^6) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_right _ hK1) hsum) B
    _ = _ := by change _=B+widthResourceCoefficient M*X^12;unfold widthResourceCoefficient;ring

#print axioms loop_width_polynomial
end Maxwell.Continuum.Parameters.OuterMachine
