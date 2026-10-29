import Maxwell.Realization.IntegerScales

/-! The emitted finite format and rational values satisfy literal logarithmic
width bounds in the exact convention used by Main.Resources. -/
namespace Maxwell.Realization

theorem clog_le_inputBitLength (m : ℕ) : Nat.clog 2 m ≤ Maxwell.unsignedBitLength (2+m) := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1<2) (2+m)
  have hz : 2+m≠0 := by omega
  unfold Maxwell.unsignedBitLength
  simp only [hz, ↓reduceIte, Nat.log2_eq_log_two]
  omega

theorem inputBitLength_pos (m : ℕ) : 1 ≤ Maxwell.unsignedBitLength (2+m) := by
  unfold Maxwell.unsignedBitLength
  have hz : 2+m≠0 := by omega
  simp only [hz, ↓reduceIte]
  omega

/-- The decoder integer range and fractional unit are selected explicitly. -/
def polynomialFormat (m integerExponent : ℕ) (budget : ℚ) (hbudget : 0<budget) :
    Target.FixedPointFormat where
  integerBits := 1+integerExponent*Nat.clog 2 m
  fractionalBits := precisionBits budget hbudget

theorem polynomialFormat_inRange (m integerExponent : ℕ) (budget : ℚ) (hbudget : 0<budget)
    (x : ℝ) (hx : |x|≤(m:ℝ)^integerExponent) :
    (polynomialFormat m integerExponent budget hbudget).InRange x := by
  have hm : (m:ℝ)≤(2:ℝ)^Nat.clog 2 m := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) m
  have hb : (m:ℝ)^integerExponent ≤ (2:ℝ)^(integerExponent*Nat.clog 2 m) := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤m) hm integerExponent
    simpa only [←pow_mul, Nat.mul_comm (Nat.clog 2 m) integerExponent] using h
  have hpos : (0:ℝ)<2^(integerExponent*Nat.clog 2 m) := by positivity
  have ha := hx.trans hb
  obtain ⟨hlo,hhi⟩ := abs_le.mp ha
  unfold Target.FixedPointFormat.InRange polynomialFormat
  simp only [pow_add, pow_one]
  constructor <;> linarith

/-- The selected format meets the exact logarithmic width convention used by
the final realization contract, with an effectively computed coefficient. -/
theorem polynomialFormat_width (m integerExponent c e : ℕ) (budget : ℚ) (hbudget : 0<budget)
    (hbound : budget⁻¹≤(2:ℚ)^c*(m:ℚ)^e) :
    (polynomialFormat m integerExponent budget hbudget).width ≤
      (2+c+integerExponent+e)*Maxwell.unsignedBitLength (2+m) := by
  have hp := precisionBits_le_clog budget hbudget m c e hbound
  have hb := clog_le_inputBitLength m
  have hpos := inputBitLength_pos m
  unfold Target.FixedPointFormat.width polynomialFormat
  have hi := Nat.mul_le_mul_left integerExponent hb
  have he := Nat.mul_le_mul_left e hb
  have hc := Nat.mul_le_mul_left (2+c) hpos
  nlinarith

/-- Every mathematical field satisfying the proved polynomial amplitude
bound fits the same emitted finite format. -/
theorem polynomialFormat_fits {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (m integerExponent : ℕ) (budget : ℚ) (hbudget : 0<budget)
    (hformat : D.format=polynomialFormat m integerExponent budget hbudget)
    (y : ι→ℝ) (hy : ∀ j, |y (D.coordinate j)|≤(m:ℝ)^integerExponent) : D.Fits y := by
  intro j
  rw [hformat]
  exact polynomialFormat_inRange m integerExponent budget hbudget _ (hy j)

/-- Actual rounded rational coefficients have logarithmic reduced numerator
and denominator size; canonical reduction introduces no extra budget. -/
theorem selectedRound_short (m integerExponent c e : ℕ) (budget : ℚ) (hbudget : 0<budget)
    (hbound : budget⁻¹≤(2:ℚ)^c*(m:ℚ)^e) (x : ℚ) (hx : |x|≤(m:ℚ)^integerExponent) :
    Source.ShortRational
      (((3+2*c+integerExponent+2*e)*Maxwell.unsignedBitLength (2+m):ℕ):ℝ)
      (selectedRound budget hbudget x).value := by
  have hm : (m:ℚ)≤(2:ℚ)^Nat.clog 2 m := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) m
  have hx2 : |x|≤(2:ℚ)^(integerExponent*Nat.clog 2 m) := by
    apply hx.trans
    have h := pow_le_pow_left₀ (by positivity : (0:ℚ)≤m) hm integerExponent
    simpa only [←pow_mul, Nat.mul_comm (Nat.clog 2 m) integerExponent] using h
  have hsize := selectedRound_rationalBitLength budget hbudget x (integerExponent*Nat.clog 2 m) hx2
  have hp := precisionBits_le_clog budget hbudget m c e hbound
  have hb := clog_le_inputBitLength m
  have hpos := inputBitLength_pos m
  have htotal : Maxwell.rationalBitLength (selectedRound budget hbudget x).value ≤
      (3+2*c+integerExponent+2*e)*Maxwell.unsignedBitLength (2+m) := by
    have hi := Nat.mul_le_mul_left integerExponent hb
    have he := Nat.mul_le_mul_left (2*e) hb
    have hc := Nat.mul_le_mul_left (3+2*c) hpos
    nlinarith
  constructor <;> exact_mod_cast (show _ ≤ (3+2*c+integerExponent+2*e)*Maxwell.unsignedBitLength (2+m) from
    (by unfold Maxwell.rationalBitLength at htotal; omega))

end Maxwell.Realization
