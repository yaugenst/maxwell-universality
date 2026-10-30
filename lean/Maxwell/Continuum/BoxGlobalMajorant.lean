import Maxwell.Continuum.MasterConstants

/-! Symbolic absorption of the concrete bulk and boundary residual
coefficients into the manuscript's global majorant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open MasterConstants

def residualEnvelope (N J m K a L : ℝ) : ℝ :=
  (1+N)^2*(1+J+m)^2*(1+K)^4*(1+a)^2*L^100

def globalMajorant (N J m K α L : ℝ) : ℝ := Cs^32*residualEnvelope N J m K α⁻¹ L

theorem residualEnvelope_factors {N J m K a L : ℝ}
    (hN : 0 ≤ N) (hJ : 0 ≤ J) (hm : 0 ≤ m) (hK : 0 ≤ K) (ha : 0 ≤ a) (hL : 1 ≤ L) :
    (1+J)*K^2*a*L^4 ≤ residualEnvelope N J m K a L ∧
    (1+J)*(1+m) ≤ residualEnvelope N J m K a L ∧
    N*K^2*a*L^8 ≤ residualEnvelope N J m K a L := by
  have hN1 : (1 : ℝ) ≤ (1+N)^2 := one_le_pow₀ (by linarith)
  have hN2 : N ≤ (1+N)^2 := by nlinarith [sq_nonneg N]
  have hB1 : 1 ≤ (1+J+m)^2 := one_le_pow₀ (by linarith)
  have hB2 : 1+J ≤ (1+J+m)^2 := by nlinarith [sq_nonneg (J+m)]
  have hB3 : (1+J)*(1+m) ≤ (1+J+m)^2 := by nlinarith [sq_nonneg J, sq_nonneg m, mul_nonneg hJ hm]
  have hK1 : (1 : ℝ) ≤ (1+K)^4 := one_le_pow₀ (by linarith)
  have hK2 : K^2 ≤ (1+K)^4 := by
    apply (pow_le_pow_left₀ hK (show K ≤ 1+K by linarith) 2).trans
    exact pow_le_pow_right₀ (by linarith) (by decide : 2 ≤ 4)
  have ha1 : (1 : ℝ) ≤ (1+a)^2 := one_le_pow₀ (by linarith)
  have ha2 : a ≤ (1+a)^2 := by nlinarith [sq_nonneg a]
  have hL1 : (1 : ℝ) ≤ L^100 := one_le_pow₀ hL
  have hL4 : L^4 ≤ L^100 := pow_le_pow_right₀ hL (by decide)
  have hL8 : L^8 ≤ L^100 := pow_le_pow_right₀ hL (by decide)
  unfold residualEnvelope
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = 1*(1+J)*K^2*a*L^4 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = 1*((1+J)*(1+m))*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = N*1*K^2*a*L^8 := by ring
      _ ≤ _ := by gcongr

theorem global_majorant_absorption {C N J m K a L : ℝ}
    (hC : (2 : ℝ)^28 ≤ C) (hN : 0 ≤ N) (hJ : 0 ≤ J) (hm : 0 ≤ m)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hL : 1 ≤ L) :
    C*(1+J)*(C^4*K^2*a*L^4+1+m)+(2 : ℝ)^26*C^5*N*K^2*a*L^8 ≤
      C^32*residualEnvelope N J m K a L := by
  have hC1 : 1 ≤ C := le_trans (by norm_num) hC
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hC5 : C ≤ C^5 := by simpa only [pow_one] using pow_le_pow_right₀ hC1 (by decide : 1 ≤ 5)
  have hF := residualEnvelope_factors hN hJ hm hK ha hL
  have hF0 : 0 ≤ residualEnvelope N J m K a L := by
    unfold residualEnvelope
    positivity
  have hfirst : C*(1+J)*(C^4*K^2*a*L^4+1+m) ≤ 2*C^5*residualEnvelope N J m K a L := by
    calc
      _ = C^5*((1+J)*K^2*a*L^4)+C*((1+J)*(1+m)) := by ring
      _ ≤ C^5*residualEnvelope N J m K a L+C^5*residualEnvelope N J m K a L :=
        add_le_add (mul_le_mul_of_nonneg_left hF.1 (by positivity))
          (mul_le_mul hC5 hF.2.1 (by positivity) (by positivity))
      _ = _ := by ring
  have hsecond : (2 : ℝ)^26*C^5*N*K^2*a*L^8 ≤ (2 : ℝ)^26*C^5*residualEnvelope N J m K a L := by
    convert mul_le_mul_of_nonneg_left hF.2.2 (show 0 ≤ (2 : ℝ)^26*C^5 by positivity) using 1
    ring
  have hcoeff : (2+(2 : ℝ)^26)*C^5 ≤ C^32 := by
    calc
      _ ≤ C*C^5 := mul_le_mul_of_nonneg_right ((by norm_num : 2+(2 : ℝ)^26 ≤ 2^28).trans hC) (by positivity)
      _ = C^6 := by ring
      _ ≤ _ := pow_le_pow_right₀ hC1 (by decide)
  calc
    _ ≤ 2*C^5*residualEnvelope N J m K a L+(2 : ℝ)^26*C^5*residualEnvelope N J m K a L := add_le_add hfirst hsecond
    _ = ((2+(2 : ℝ)^26)*C^5)*residualEnvelope N J m K a L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hF0

#print axioms global_majorant_absorption

end Maxwell.Continuum.BoxCutoff
