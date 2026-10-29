import Maxwell.Realization.IntegerScales

/-! Literal natural exponents for the full physical inverse and selected
residual tolerance. All fixed coefficients are explicitly absorbed for m≥2. -/
namespace Maxwell.Realization

private theorem bound_mul (m a b : ℕ) {x y : ℚ}
    (hx : x≤(m:ℚ)^a) (hy : y≤(m:ℚ)^b) (hy0 : 0≤y) :
    x*y≤(m:ℚ)^(a+b) := by
  rw [pow_add]
  exact mul_le_mul hx hy hy0 (by positivity)

private theorem bound_add (m a b : ℕ) (hm : 2≤m) {x y : ℚ}
    (hx : x≤(m:ℚ)^a) (hy : y≤(m:ℚ)^b) : x+y≤(m:ℚ)^(max a b+1) := by
  have hm1 : (1:ℚ)≤m := by exact_mod_cast (show 1≤m by omega)
  have ha := hx.trans (pow_le_pow_right₀ hm1 (le_max_left a b))
  have hb := hy.trans (pow_le_pow_right₀ hm1 (le_max_right a b))
  rw [pow_succ]
  have htwo : (2:ℚ)≤m := by exact_mod_cast hm
  nlinarith [mul_le_mul_of_nonneg_left htwo (show (0:ℚ)≤(m:ℚ)^max a b by positivity)]

private theorem bound_square (m a : ℕ) {x : ℚ} (hx0 : 0≤x) (hx : x≤(m:ℚ)^a) :
    x^2≤(m:ℚ)^(2*a) := by
  have h := pow_le_pow_left₀ hx0 hx 2
  simpa only [←pow_mul, Nat.mul_comm a 2] using h

private theorem power_two_bound (m e : ℕ) (hm : 2≤m) : (2:ℚ)^e≤(m:ℚ)^e :=
  pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _

/-- A positive fixed rational has a literal input-power bound whose natural
exponent is obtained by the exact precision search. -/
def constantExponent (x : ℚ) (hx : 0<x) : ℕ := precisionBits x⁻¹ (inv_pos.mpr hx)

theorem constant_le_input_power (x : ℚ) (hx : 0<x) (m : ℕ) (hm : 2≤m) :
    x≤(m:ℚ)^constantExponent x hx := by
  simpa only [constantExponent, inv_inv] using inverse_le_input_pow x⁻¹ (inv_pos.mpr hx) m hm

namespace PhysicalConstants

def backgroundExponent (dimensionExponent detuningExponent : ℕ) : ℕ :=
  6+2*max 1 dimensionExponent+detuningExponent

/-- The background inverse uses the actual final field count N. -/
theorem backgroundInverseBudget_literal (P : PhysicalConstants) (ζ : ℚ) (hζ : 0<ζ)
    (m N n t : ℕ) (hm : 2≤m) (hN : (N:ℚ)≤(m:ℚ)^n)
    (hτ : (P.detuningWidth ζ hζ)⁻¹≤(m:ℚ)^t) :
    P.backgroundInverseBudget ζ hζ m N≤(m:ℚ)^(backgroundExponent n t) := by
  have hsum := bound_add m 1 n hm (x := (m:ℚ)) (y := N) (by simp) hN
  have hsquare := bound_square m (max 1 n+1) (by positivity) hsum
  have h16 : (16:ℚ)≤(m:ℚ)^4 := by convert power_two_bound m 4 hm using 1; norm_num
  have h := bound_mul m (4+2*(max 1 n+1)) t
    (bound_mul m 4 (2*(max 1 n+1)) h16 hsquare (by positivity)) hτ
      (inv_nonneg.mpr (P.detuningWidth_pos ζ hζ).le)
  convert h using 1
  · unfold backgroundInverseBudget
    ring
  · unfold backgroundExponent
    congr 1
    omega

def modeExponent (P : PhysicalConstants) (logicalExponent alphaExponent : ℕ) : ℕ :=
  3+max (5+logicalExponent+alphaExponent)
    (constantExponent (2/P.defectGap) (div_pos (by norm_num) P.defectGap_pos))

def fullExponent (P : PhysicalConstants) (logicalExponent alphaExponent backgroundExponent : ℕ) : ℕ :=
  2*backgroundExponent+P.modeExponent logicalExponent alphaExponent+1

/-- The weighted-mode inverse budget has a literal polynomial bound. -/
theorem modeInverseBudget_literal (P : PhysicalConstants) (K α : ℚ) (hK0 : 0≤K) (hα : 0<α)
    (m k a : ℕ) (hm : 2≤m) (hK : K≤(m:ℚ)^k) (hαinv : α⁻¹≤(m:ℚ)^a) :
    P.modeInverseBudget K α≤(m:ℚ)^(P.modeExponent k a) := by
  have h32 : (32:ℚ)≤(m:ℚ)^5 := by convert power_two_bound m 5 hm using 1; norm_num
  have hfirst := bound_mul m (5+k) a
    (bound_mul m 5 k h32 hK (by positivity)) hαinv (inv_nonneg.mpr hα.le)
  have hgap := constant_le_input_power (2/P.defectGap) (div_pos (by norm_num) P.defectGap_pos) m hm
  have hsum := bound_add m (5+k+a) _ hm hfirst hgap
  have h4 : (4:ℚ)≤(m:ℚ)^2 := by convert power_two_bound m 2 hm using 1; norm_num
  have hsum0 : 0≤32*K*α⁻¹+2/P.defectGap := by
    have hJ := P.defectGap_pos
    positivity
  have h := bound_mul m 2 _ h4 hsum hsum0
  convert h using 1
  · unfold modeInverseBudget
    ring
  · unfold modeExponent
    congr 1
    omega

/-- Full physical inverse amplification is controlled, not just the terminal
Schur response. -/
theorem fullInverseBudget_literal (P : PhysicalConstants) (K α L : ℚ)
    (hK0 : 0≤K) (hα : 0<α) (hL0 : 0≤L) (m k a b : ℕ) (hm : 2≤m)
    (hK : K≤(m:ℚ)^k) (hαinv : α⁻¹≤(m:ℚ)^a) (hL : L≤(m:ℚ)^b) :
    P.fullInverseBudget K α L≤(m:ℚ)^(P.fullExponent k a b) := by
  have hM := P.modeInverseBudget_literal K α hK0 hα m k a hm hK hαinv
  have hM0 : 0≤P.modeInverseBudget K α := by
    have hgap := P.defectGap_pos
    unfold modeInverseBudget
    positivity
  have hprod := bound_mul m (2*b) (P.modeExponent k a) (bound_square m b hL0 hL) hM hM0
  have h := bound_add m b (2*b+P.modeExponent k a) hm hL hprod
  have he : max b (2*b+P.modeExponent k a)=2*b+P.modeExponent k a := max_eq_right (by omega)
  simpa only [he, fullInverseBudget, fullExponent] using h

def toleranceExponent (P : PhysicalConstants) (errorExponent backgroundExponent : ℕ) : ℕ :=
  14+constantExponent P.rowBound P.rowBound_pos+
    constantExponent P.inverseWeightBound P.inverseWeightBound_pos+backgroundExponent+errorExponent

/-- The actual emitted dyadic residual tolerance satisfies a literal
inverse-polynomial lower bound on every draw. -/
theorem residualUnit_inverse_literal (P : PhysicalConstants) (ε L : ℚ)
    (hε : 0<ε) (hL : 0<L) (m e b : ℕ) (hm : 2≤m)
    (hεinv : ε⁻¹≤(m:ℚ)^e) (hLb : L≤(m:ℚ)^b) :
    (P.residualUnit ε L hε hL)⁻¹≤(m:ℚ)^(P.toleranceExponent e b) := by
  have h8192 : (8192:ℚ)≤(m:ℚ)^13 := by convert power_two_bound m 13 hm using 1; norm_num
  have hJ := constant_le_input_power P.rowBound P.rowBound_pos m hm
  have hW := constant_le_input_power P.inverseWeightBound P.inverseWeightBound_pos m hm
  have h1 := bound_mul m 13 _ h8192 hJ P.rowBound_pos.le
  have h2 := bound_mul m _ _ h1 hW P.inverseWeightBound_pos.le
  have h3 := bound_mul m _ b h2 hLb hL.le
  have h4 := bound_mul m _ e h3 hεinv (inv_nonneg.mpr hε.le)
  have hb : (P.residualBudget ε L)⁻¹≤(m:ℚ)^
      (13+constantExponent P.rowBound P.rowBound_pos+
        constantExponent P.inverseWeightBound P.inverseWeightBound_pos+b+e) := by
    convert h4 using 1
    unfold residualBudget
    rw [inv_div]
    ring
  have h := precisionUnit_inverse_literal (P.residualBudget ε L) (P.residualBudget_pos ε L hε hL) m _ hm hb
  unfold residualUnit
  convert h using 1
  unfold toleranceExponent
  congr 1
  omega

theorem residualUnit_lower_literal (P : PhysicalConstants) (ε L : ℚ)
    (hε : 0<ε) (hL : 0<L) (m e b : ℕ) (hm : 2≤m)
    (hεinv : ε⁻¹≤(m:ℚ)^e) (hLb : L≤(m:ℚ)^b) :
    1/(m:ℚ)^(P.toleranceExponent e b)≤P.residualUnit ε L hε hL := by
  have h := P.residualUnit_inverse_literal ε L hε hL m e b hm hεinv hLb
  have hu := (P.residualUnit_bounds ε L hε hL).1
  have hp : (0:ℚ)<(m:ℚ)^(P.toleranceExponent e b) := by positivity
  have hi := (inv_le_inv₀ hp (inv_pos.mpr hu)).mpr h
  simpa only [inv_inv, one_div] using hi

/-- An actual final-dimension bound also controls the max-one convention. -/
private theorem count_max_bound (m N n : ℕ) (hm : 2≤m) (hN : (N:ℚ)≤(m:ℚ)^n) :
    max 1 (N:ℚ)≤(m:ℚ)^n :=
  max_le (one_le_pow₀ (by exact_mod_cast (show 1≤m by omega))) hN

def sourcePrecisionExponent (backgroundExponent dimensionExponent alphaExponent errorExponent : ℕ) : ℕ :=
  15+backgroundExponent+dimensionExponent+alphaExponent+errorExponent

/-- The emitted source uses the actual final dimension in its grid budget. -/
theorem sourceBudget_inverse_literal (α ε L : ℚ) (hα : 0<α) (hε : 0<ε) (hL : 0<L)
    (m N a e b n : ℕ) (hm : 2≤m)
    (hαinv : α⁻¹≤(m:ℚ)^a) (hεinv : ε⁻¹≤(m:ℚ)^e)
    (hLb : L≤(m:ℚ)^b) (hN : (N:ℚ)≤(m:ℚ)^n) :
    (sourceBudget α ε L N)⁻¹≤(m:ℚ)^(sourcePrecisionExponent b n a e) := by
  have h32768 : (32768:ℚ)≤(m:ℚ)^15 := by convert power_two_bound m 15 hm using 1; norm_num
  have h1 := bound_mul m 15 b h32768 hLb hL.le
  have h2 := bound_mul m _ n h1 (count_max_bound m N n hm hN) (by positivity)
  have h3 := bound_mul m _ a h2 hαinv (inv_nonneg.mpr hα.le)
  have h4 := bound_mul m _ e h3 hεinv (inv_nonneg.mpr hε.le)
  unfold sourcePrecisionExponent
  convert h4 using 1
  unfold sourceBudget
  rw [inv_div]
  ring

def readoutPrecisionExponent (P : PhysicalConstants) (sampleExponent errorExponent : ℕ) : ℕ :=
  13+constantExponent (max 1 P.incrementBound) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))+
    sampleExponent+errorExponent

theorem readoutBudget_inverse_literal (P : PhysicalConstants) (ε : ℚ) (hε : 0<ε)
    (m p e n : ℕ) (hm : 2≤m) (hεinv : ε⁻¹≤(m:ℚ)^e) (hp : (p:ℚ)≤(m:ℚ)^n) :
    (P.readoutBudget ε p)⁻¹≤(m:ℚ)^(P.readoutPrecisionExponent n e) := by
  have h8192 : (8192:ℚ)≤(m:ℚ)^13 := by convert power_two_bound m 13 hm using 1; norm_num
  have hv := constant_le_input_power (max 1 P.incrementBound)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m hm
  have h1 := bound_mul m 13 _ h8192 hv (by positivity)
  have h2 := bound_mul m _ n h1 (count_max_bound m p n hm hp) (by positivity)
  have h3 := bound_mul m _ e h2 hεinv (inv_nonneg.mpr hε.le)
  unfold readoutPrecisionExponent
  convert h3 using 1
  unfold readoutBudget
  rw [inv_div]
  ring

def calibrationPrecisionExponent (P : PhysicalConstants)
    (backgroundExponent alphaUpperExponent fullInverseExponent errorExponent : ℕ) : ℕ :=
  max (15+constantExponent P.rowBound P.rowBound_pos+backgroundExponent+
    constantExponent P.weightMinimum⁻¹ (inv_pos.mpr P.weightMinimum_pos)+errorExponent)
    (10+constantExponent P.incrementBound P.incrementBound_pos+alphaUpperExponent+
      constantExponent P.rowBound P.rowBound_pos+
      constantExponent P.inverseWeightBound P.inverseWeightBound_pos+fullInverseExponent+errorExponent)

/-- Both independently calibrated uses of the local mode are accounted for
in one explicit natural precision exponent. -/
theorem calibrationBudget_inverse_literal (P : PhysicalConstants) (ε α L QA : ℚ)
    (hε : 0<ε) (hα : 0<α) (hL : 0<L) (hQA : 0<QA)
    (m e a b q : ℕ) (hm : 2≤m) (hεinv : ε⁻¹≤(m:ℚ)^e)
    (hαb : α≤(m:ℚ)^a) (hLb : L≤(m:ℚ)^b) (hQb : QA≤(m:ℚ)^q) :
    (P.calibrationBudget ε α L QA)⁻¹≤(m:ℚ)^(P.calibrationPrecisionExponent b a q e) := by
  have hm1 : (1:ℚ)≤m := by exact_mod_cast (show 1≤m by omega)
  have hJ := constant_le_input_power P.rowBound P.rowBound_pos m hm
  have hW := constant_le_input_power P.inverseWeightBound P.inverseWeightBound_pos m hm
  have hv := constant_le_input_power P.incrementBound P.incrementBound_pos m hm
  have hw := constant_le_input_power P.weightMinimum⁻¹ (inv_pos.mpr P.weightMinimum_pos) m hm
  have hc1 : (32768:ℚ)≤(m:ℚ)^15 := by convert power_two_bound m 15 hm using 1; norm_num
  have hc2 : (1024:ℚ)≤(m:ℚ)^10 := by convert power_two_bound m 10 hm using 1; norm_num
  have h1 := bound_mul m _ e
    (bound_mul m _ _
      (bound_mul m _ b (bound_mul m 15 _ hc1 hJ P.rowBound_pos.le) hLb hL.le)
      hw (inv_nonneg.mpr P.weightMinimum_pos.le)) hεinv (inv_nonneg.mpr hε.le)
  have h2 := bound_mul m _ e
    (bound_mul m _ q
      (bound_mul m _ _
        (bound_mul m _ _
          (bound_mul m _ a (bound_mul m 10 _ hc2 hv P.incrementBound_pos.le) hαb hα.le)
          hJ P.rowBound_pos.le)
        hW P.inverseWeightBound_pos.le)
      hQb hQA.le)
    hεinv (inv_nonneg.mpr hε.le)
  have he1 : (P.weightMinimum*ε/(32768*P.rowBound*L))⁻¹ =
      32768*P.rowBound*L*P.weightMinimum⁻¹*ε⁻¹ := by rw [inv_div]; ring
  have he2 : (ε/(1024*P.incrementBound*α*P.rowBound*P.inverseWeightBound*QA))⁻¹ =
      1024*P.incrementBound*α*P.rowBound*P.inverseWeightBound*QA*ε⁻¹ := by rw [inv_div]; ring
  unfold calibrationBudget calibrationPrecisionExponent
  by_cases hc : P.weightMinimum*ε/(32768*P.rowBound*L) ≤
      ε/(1024*P.incrementBound*α*P.rowBound*P.inverseWeightBound*QA)
  · rw [min_eq_left hc, he1]
    exact h1.trans (pow_le_pow_right₀ hm1 (le_max_left _ _))
  · rw [min_eq_right (le_of_not_ge hc), he2]
    exact h2.trans (pow_le_pow_right₀ hm1 (le_max_right _ _))

def conditionExponent (P : PhysicalConstants) (logicalExponent alphaExponent backgroundExponent : ℕ) : ℕ :=
  constantExponent P.rowBound P.rowBound_pos+P.fullExponent logicalExponent alphaExponent backgroundExponent

/-- Multiplication by the actual fixed matrix norm bound gives a literal
condition-number budget. -/
theorem conditionBudget_literal (P : PhysicalConstants) (K α L : ℚ)
    (hK0 : 0≤K) (hα : 0<α) (hL : 0<L) (m k a b : ℕ) (hm : 2≤m)
    (hK : K≤(m:ℚ)^k) (hαinv : α⁻¹≤(m:ℚ)^a) (hLb : L≤(m:ℚ)^b) :
    P.rowBound*P.fullInverseBudget K α L≤(m:ℚ)^(P.conditionExponent k a b) := by
  have hfull := P.fullInverseBudget_literal K α L hK0 hα hL.le m k a b hm hK hαinv hLb
  have hfull0 : 0≤P.fullInverseBudget K α L := by
    have hg := P.defectGap_pos
    unfold fullInverseBudget modeInverseBudget
    positivity
  exact bound_mul m _ _ (constant_le_input_power P.rowBound P.rowBound_pos m hm) hfull hfull0

end PhysicalConstants
end Maxwell.Realization
