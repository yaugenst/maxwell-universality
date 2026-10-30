import Maxwell.Continuum.BoxGlobalMajorant
import Maxwell.Continuum.BoundaryCellH1

/-! The global residual budget uses precisely the manuscript's Xi,
with no numerical evaluation of its enormous fixed constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BoxCutoff

open CellGauge MasterConstants

attribute [local irreducible] Cs

theorem residual_two_scales {A B X p q r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : r ≤ p) (hX : A+B ≤ X) : A*p+B*(q+r) ≤ X*(p+q) := by
  calc
    _ ≤ A*p+B*(q+p) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hr) hB)
    _ ≤ (A+B)*(p+q) := by nlinarith only [mul_nonneg hA hq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hX (add_nonneg hp hq)

theorem box_residual_budget {N J m K α L b F H T G : ℝ}
    (hN : 0 ≤ N) (hJ : 0 ≤ J) (hm : 0 ≤ m) (hK : 0 ≤ K) (hα : 0 < α)
    (hL : 1 ≤ L) (hG : 0 ≤ G) (hFH : F ≤ H)
    (hH : H ≤ Cs^4*K^2*α⁻¹*L^4*G) (hT : T ≤ (1+m)*G) :
    Cs*(1+J)*Real.exp (-cs*L^(1/3 : ℝ))*(F+T)+
      (2 : ℝ)^26*boundaryCellMajorant L b N*H ≤
      globalMajorant N J m K α L*(Real.exp (-cs*L^(1/3 : ℝ))+Real.exp (-cs*b/L))*G := by
  let A := Cs*(1+J)*(Cs^4*K^2*α⁻¹*L^4+1+m)
  let B := (2 : ℝ)^26*Cs^5*N*K^2*α⁻¹*L^8
  have ha : 0 ≤ α⁻¹ := (inv_pos.mpr hα).le
  have hC := Cs_pos
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hX : A+B ≤ globalMajorant N J m K α L := by
    exact global_majorant_absorption
      (fixed_power_le_Cs (by have := exponent_large; omega : 28 ≤ MasterConstants.exponent)) hN hJ hm hK ha hL
  have hbulk : Cs*(1+J)*Real.exp (-cs*L^(1/3 : ℝ))*(F+T) ≤
      A*Real.exp (-cs*L^(1/3 : ℝ))*G := by
    have hh := add_le_add (hFH.trans hH) hT
    apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ Cs*(1+J)*Real.exp (-cs*L^(1/3 : ℝ)) by positivity)).trans_eq
    dsimp only [A]
    ring
  have hboundary : (2 : ℝ)^26*boundaryCellMajorant L b N*H ≤
      B*(Real.exp (-cs*b/L)+Real.exp (-cs*L))*G := by
    have hb0 := boundaryCellMajorant_nonneg (L := L) (b := b) hN
    apply (mul_le_mul_of_nonneg_left hH (show 0 ≤ (2 : ℝ)^26*boundaryCellMajorant L b N by positivity)).trans_eq
    dsimp only [B, boundaryCellMajorant]
    ring
  have hexp : Real.exp (-cs*L) ≤ Real.exp (-cs*L^(1/3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (Real.rpow_le_self_of_one_le hL (by norm_num : (1/3 : ℝ) ≤ 1)) (neg_nonpos.mpr cs_pos.le)
  have hscale := residual_two_scales (q := Real.exp (-cs*b/L))
    hA hB (Real.exp_pos _).le (Real.exp_pos _).le hexp hX
  calc
    _ ≤ A*Real.exp (-cs*L^(1/3 : ℝ))*G+B*(Real.exp (-cs*b/L)+Real.exp (-cs*L))*G :=
      add_le_add hbulk hboundary
    _ = (A*Real.exp (-cs*L^(1/3 : ℝ))+B*(Real.exp (-cs*b/L)+Real.exp (-cs*L)))*G := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hG

#print axioms box_residual_budget

end Maxwell.Continuum.BoxCutoff
