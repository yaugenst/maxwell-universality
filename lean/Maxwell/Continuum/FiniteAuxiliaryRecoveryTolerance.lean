import Maxwell.Continuum.FiniteAuxiliaryFieldRange

/-! The paper's finite source, material, template and message tolerances
pay the actual every-field logical residual with a fixed margin. -/

namespace Maxwell.Continuum.FiniteAuxiliary

open MasterConstants
attribute [local irreducible] Cs Ls

theorem readout_strength_budget {L : ℝ} (hL : Ls ≤ L) :
    (2 : ℝ)^130*L⁻¹^2 ≤ 1 := by
  have hLp := length_pos hL
  have hL1 := length_ge_one hL
  have hp : (2 : ℝ)^130 ≤ L :=
    (power_le_Ls (by have := exponent_large; omega)).trans hL
  rw [inv_pow, mul_inv_le_iff₀ (pow_pos hLp 2), one_mul]
  nlinarith only [hp, hL1]

theorem recovery_tolerance_budget {ε G g e₀ V η δf δr merror δo ω : ℝ}
    (hε : 0 ≤ ε) (hG : 0 ≤ G) (hg : 0 ≤ g) (he0 : 0 ≤ e₀) (he1 : e₀ ≤ 1/2)
    (hGe : G*e₀ = ε/(2 : ℝ)^27) (hV0 : 0 ≤ V) (hV : V ≤ 1)
    (hη0 : 0 ≤ η) (hf0 : 0 ≤ δf)
    (hη : η ≤ 2*e₀*g) (hf : δf ≤ e₀*g/4)
    (hr : δr ≤ e₀*g/2) (hm : merror ≤ e₀*g/4)
    (ho : δo ≤ e₀/4) (hω : ω ≤ ε*g/(2 : ℝ)^26) :
    6*(V*(G*(η+δf+δr+merror))+δo*(G*(η+δf+g)))+ε*g/1024+6*ω ≤ ε*g/2 := by
  have ht : η+δf+δr+merror ≤ 3*e₀*g := by linarith only [hη, hf, hr, hm]
  have hn : η+δf+g ≤ 3*g := by
    have he := mul_le_mul_of_nonneg_right he1 hg
    linarith only [hη, hf, he, hg]
  have hfirst : V*(G*(η+δf+δr+merror)) ≤ 3*(G*e₀)*g := by
    calc
      _ ≤ V*(G*(3*e₀*g)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ht hG) hV0
      _ ≤ 1*(G*(3*e₀*g)) := mul_le_mul_of_nonneg_right hV (by positivity)
      _ = _ := by ring
  have hsecond : δo*(G*(η+δf+g)) ≤ (3/4)*(G*e₀)*g := by
    calc
      _ ≤ (e₀/4)*(G*(3*g)) := mul_le_mul ho
        (mul_le_mul_of_nonneg_left hn hG) (by positivity) (by positivity)
      _ = _ := by ring
  rw [hGe] at hfirst hsecond
  have hsg := mul_nonneg hε hg
  nlinarith only [hfirst, hsecond, hω, hsg]

theorem message_tolerance_budget {J : ℕ} {ε g : ℝ} (hε : 0 ≤ ε) (hg : 1 ≤ g) :
    (J : ℝ)*(2*(ε/((2 : ℝ)^27*max 1 (J : ℝ)))) ≤ ε*g/(2 : ℝ)^26 := by
  have hm : 0 < max 1 (J : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : (J : ℝ)/max 1 (J : ℝ) ≤ 1 := (div_le_one hm).mpr (le_max_right _ _)
  calc
    _ = (ε/(2 : ℝ)^26)*((J : ℝ)/max 1 (J : ℝ)) := by
      field_simp
    _ ≤ (ε/(2 : ℝ)^26)*1 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (ε/(2 : ℝ)^26)*g := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

#print axioms recovery_tolerance_budget
#print axioms message_tolerance_budget

end Maxwell.Continuum.FiniteAuxiliary
