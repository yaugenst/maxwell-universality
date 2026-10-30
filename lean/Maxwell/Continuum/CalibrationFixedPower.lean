import Maxwell.Continuum.CalibrationPowerStability

/-! Stability of powers of a single computed operator. The error is
an operator norm bound, so it applies to every computed iterate without
an assumption supplying an oracle error separately at each step. -/

noncomputable section

set_option maxRecDepth 4096

namespace Maxwell.Continuum.Calibration

open EffectiveMass NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem contraction_power_norm (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1)
    (v : H) (hv : ‖v‖ ≤ 1) (n : ℕ) : ‖(A^n) v‖ ≤ 1 := by
  induction n with
  | zero => simpa only [pow_zero,one_apply_eq_self] using hv
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact (A.le_of_opNorm_le hA _).trans (by simpa only [one_mul] using ih)

theorem fixed_power_error (A T : H →L[ℂ] H) {ε : ℝ}
    (hA : ‖A‖ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hT : ‖T-A‖ ≤ ε)
    (v w : H) (hv : ‖v‖ ≤ 1) (hw : ‖w-v‖ ≤ ε) (n : ℕ) :
    ‖(T^n) w-(A^n) v‖ ≤ ((2 : ℝ)^(n+1)-1)*ε := by
  have hTnorm : ‖T‖ ≤ 2 := by
    calc
      _ ≤ ‖T-A‖+‖A‖ := norm_le_norm_sub_add T A
      _ ≤ ε+1 := add_le_add hT hA
      _ ≤ 2 := by linarith
  induction n with
  | zero => simpa only [pow_zero,one_apply_eq_self,Nat.zero_add,pow_one,
      show (2 : ℝ)-1=1 by norm_num,one_mul] using hw
  | succ n ih =>
    have hid : (T^(n+1)) w-(A^(n+1)) v =
        T ((T^n) w-(A^n) v)+(T-A) ((A^n) v) := by
      simp only [pow_succ',mul_apply_eq_comp,map_sub,sub_apply]
      abel
    rw [hid]
    have he := (T-A).le_of_opNorm_le hT ((A^n) v)
    have hc := contraction_power_norm A hA v hv n
    calc
      _ ≤ ‖T ((T^n) w-(A^n) v)‖+‖(T-A) ((A^n) v)‖ := norm_add_le _ _
      _ ≤ 2*‖(T^n) w-(A^n) v‖+ε*‖(A^n) v‖ :=
        add_le_add (T.le_of_opNorm_le hTnorm _) he
      _ ≤ 2*(((2 : ℝ)^(n+1)-1)*ε)+ε*1 := by gcongr
      _ = ((2 : ℝ)^(n+1+1)-1)*ε := by rw [pow_succ]; ring

theorem fixed_power_work_budget (N n extra : ℕ) :
    2*(2 : ℝ)^(n+1)*(1/2 : ℝ)^powerWorkBits N n extra /
      (1/2 : ℝ)^(48+38*n) ≤ (1/2 : ℝ)^(N+10) := by
  have hpow : powerWorkBits N n extra = (n+2)+(48+38*n)+(N+10)+(n+extra+196) := by
    unfold powerWorkBits
    omega
  have he : 2*(2 : ℝ)^(n+1) = (2 : ℝ)^(n+2) := by rw [pow_succ]; ring
  rw [he,hpow]
  have hid : (2 : ℝ)^(n+2)*
      (1/2 : ℝ)^((n+2)+(48+38*n)+(N+10)+(n+extra+196)) /
      (1/2 : ℝ)^(48+38*n) = (1/2 : ℝ)^(N+10)*(1/2 : ℝ)^(n+extra+196) := by
    rw [show (n+2)+(48+38*n)+(N+10)+(n+extra+196) =
      (n+2)+((48+38*n)+((N+10)+(n+extra+196))) by omega]
    rw [pow_add (1/2 : ℝ) (n+2),pow_add (1/2 : ℝ) (48+38*n),
      pow_add (1/2 : ℝ) (N+10)]
    have hcancel : (2 : ℝ)^(n+2)*(1/2 : ℝ)^(n+2) = 1 := by
      rw [← mul_pow]
      norm_num
    have hd : (1/2 : ℝ)^(48+38*n) ≠ 0 := by positivity
    calc
      _ = ((2 : ℝ)^(n+2)*(1/2 : ℝ)^(n+2))*
        ((1/2 : ℝ)^(48+38*n)*((1/2 : ℝ)^(N+10)*(1/2 : ℝ)^(n+extra+196))) /
        (1/2 : ℝ)^(48+38*n) := by ring
      _ = _ := by rw [hcancel,one_mul]; exact mul_div_cancel_left₀ _ hd
  rw [hid]
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by norm_num) (by norm_num)

attribute [local irreducible] Sh muH realMode Bloch.unitary Auxiliary.resolvent
  startingVector powerOperator powerValue startingCoefficient powerIterate

theorem fixed_power_normalized_error {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (N n extra : ℕ) (T : FieldL2 →L[ℂ] FieldL2)
    (w : FieldL2)
    (hT : ‖T-powerOperator D‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra)
    (hw : ‖w-startingVector D.h_pos‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra) :
    (T^n) w ≠ 0 ∧
      ‖normalize ((T^n) w)-normalize (powerIterate D n)‖ ≤ (1/2 : ℝ)^(N+10) := by
  have herr : ‖(T^n) w-powerIterate D n‖ ≤
      (2 : ℝ)^(n+1)*(1/2 : ℝ)^powerWorkBits N n extra := by
    rw [powerIterate]
    apply (fixed_power_error (powerOperator D) T (powerOperator_norm D hh) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) hT
      (startingVector D.h_pos) w (le_of_eq (startingVector_norm D.h_pos hh)) hw n).trans
    gcongr
    linarith
  have hl := powerIterate_norm_lower D hh n
  have hlpos : 0 < (1/2 : ℝ)^(48+38*n) := by positivity
  have hb := (div_le_iff₀ hlpos).mp (fixed_power_work_budget N n extra)
  have heps : (1/2 : ℝ)^(N+10) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have herrlt : ‖(T^n) w-powerIterate D n‖ < (1/2 : ℝ)^(48+38*n) := by
    have hm := mul_le_mul_of_nonneg_right heps hlpos.le
    nlinarith
  have hy : (T^n) w ≠ 0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at herrlt
    linarith
  refine ⟨hy,?_⟩
  apply (normalize_difference _ _ hy (powerIterate_ne_zero D hh n)).trans
  apply le_trans _ (fixed_power_work_budget N n extra)
  apply div_le_div₀ (by positivity) _ hlpos hl
  exact (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (mul_assoc _ _ _).symm

theorem fixed_power_requested_error {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (N : ℕ) (T : FieldL2 →L[ℂ] FieldL2) (w : FieldL2)
    (hT : ‖T-powerOperator D‖ ≤ (1/2 : ℝ)^powerWorkPrecision N)
    (hw : ‖w-startingVector D.h_pos‖ ≤ (1/2 : ℝ)^powerWorkPrecision N) :
    (T^(powerSteps N)) w ≠ 0 ∧
      ‖normalize ((T^(powerSteps N)) w)-realMode D hh‖ ≤ (1/2 : ℝ)^N := by
  have he := fixed_power_normalized_error D hh N (powerSteps N)
    (Nat.clog 2 (powerSteps N+1)) T w hT hw
  refine ⟨he.1,?_⟩
  apply (norm_sub_le_norm_sub_add_norm_sub _ (normalize (powerIterate D (powerSteps N))) _).trans
  apply (add_le_add he.2 (powerIterate_requested_error D hh N)).trans
  rw [pow_add,pow_add]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

#print axioms fixed_power_requested_error

end Maxwell.Continuum.Calibration
