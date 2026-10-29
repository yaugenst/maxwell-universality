import Maxwell.Realization.Precision

/-! Rounding scalar-cell increments while preserving reciprocal tuning and
material headroom. The construction acts on scalar values, never averaged
edge masses. -/
namespace Maxwell.Realization

/-- A single grid satisfies reciprocal accuracy and the reserved scalar
increment interval simultaneously. -/
def scalarBudget (lower ζ reserve : ℚ) : ℚ :=
  min lower (min (lower^2*ζ^2/2) (2*reserve))

theorem scalarBudget_pos (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve) :
    0 < scalarBudget lower ζ reserve := by unfold scalarBudget; positivity

def scalarRound (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve) (v : ℚ) :=
  selectedRound (scalarBudget lower ζ reserve) (scalarBudget_pos lower ζ reserve hlower hζ hreserve) v

/-- The actual emitted dyadic increment remains positive, stays within the
reserved interval, and has reciprocal error at mostζ²/2. -/
theorem scalarRound_bounds (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v : ℚ) (hv : lower ≤ v) :
    let w := (scalarRound lower ζ reserve hlower hζ hreserve v).value
    0 < w ∧ |w-v| ≤ reserve ∧ |w⁻¹-v⁻¹| ≤ ζ^2/2 := by
  let w := (scalarRound lower ζ reserve hlower hζ hreserve v).value
  have he := selectedRound_error (scalarBudget lower ζ reserve)
    (scalarBudget_pos lower ζ reserve hlower hζ hreserve) v
  change |w-v| ≤ scalarBudget lower ζ reserve / 2 at he
  have hb1 : scalarBudget lower ζ reserve ≤ lower := min_le_left _ _
  have hb2 : scalarBudget lower ζ reserve ≤ lower^2*ζ^2/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hb3 : scalarBudget lower ζ reserve ≤ 2*reserve :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hlow : lower/2 ≤ w := by have hh := (abs_le.mp he).1; linarith
  have hw : 0 < w := by linarith
  have hv0 : 0 < v := hlower.trans_le hv
  refine ⟨hw, by linarith, ?_⟩
  change |w⁻¹-v⁻¹| ≤ ζ^2/2
  rw [inv_sub_inv (ne_of_gt hw) (ne_of_gt hv0), abs_div,
    abs_of_pos (mul_pos hw hv0), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hw hv0)).mpr
  have hm : lower^2/2 ≤ w*v := by
    have h := mul_le_mul hlow hv hlower.le hw.le
    nlinarith
  have hz := mul_le_mul_of_nonneg_right hm (sq_nonneg ζ)
  nlinarith

/-- Uniform scalar assignment to the selected cells preserves the actual
material interval. The frequency factor is exactly1/64. -/
theorem scalarRound_material_bounds (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v background : ℚ) (hv : lower ≤ v)
    (hlo : 1 + 64*reserve ≤ background + 64*v)
    (hhi : background + 64*v ≤ 25 - 64*reserve) :
    1 ≤ background + 64*(scalarRound lower ζ reserve hlower hζ hreserve v).value ∧
      background + 64*(scalarRound lower ζ reserve hlower hζ hreserve v).value ≤ 25 := by
  have he := (scalarRound_bounds lower ζ reserve hlower hζ hreserve v hv).2.1
  obtain ⟨ha,hb⟩ := abs_le.mp he
  constructor <;> linarith

/-- Adding the selected scalar increment to a dyadic background emits an
actual dyadic scalar cell with an explicit common denominator. -/
def scalarCellDyadic (p : ℕ) (background : Maxwell.Dyadic p)
    (lower ζ reserve : ℚ) (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v : ℚ) : Maxwell.Dyadic
      (p + precisionBits (scalarBudget lower ζ reserve) (scalarBudget_pos lower ζ reserve hlower hζ hreserve)) :=
  ⟨background.numerator * 2^(precisionBits (scalarBudget lower ζ reserve)
      (scalarBudget_pos lower ζ reserve hlower hζ hreserve)) +
    64*(scalarRound lower ζ reserve hlower hζ hreserve v).numerator*2^p⟩

theorem scalarCellDyadic_value (p : ℕ) (background : Maxwell.Dyadic p)
    (lower ζ reserve : ℚ) (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve) (v : ℚ) :
    (scalarCellDyadic p background lower ζ reserve hlower hζ hreserve v).value =
      background.value + 64*(scalarRound lower ζ reserve hlower hζ hreserve v).value := by
  simp only [scalarCellDyadic, Maxwell.Dyadic.value, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, pow_add]
  field_simp

/-- Calibration and scalar-cell rounding each use half of the final
reciprocal tuning allowance. -/
theorem scalarRound_tuning (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v target : ℚ) (hv : lower ≤ v) (hcal : |v⁻¹-target| ≤ ζ^2/2) :
    |(scalarRound lower ζ reserve hlower hζ hreserve v).value⁻¹-target| ≤ ζ^2 := by
  have hround := (scalarRound_bounds lower ζ reserve hlower hζ hreserve v hv).2.2
  have htriangle := abs_sub_le (scalarRound lower ζ reserve hlower hζ hreserve v).value⁻¹ v⁻¹ target
  linarith

/-- The rounded scalar cells retain the complete subsequently used uniform
detuning interval. -/
theorem scalarRound_material_headroom (lower ζ reserve τ : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v background : ℚ) (hv : lower ≤ v)
    (hlo : 1 + 64*reserve ≤ background + 64*v)
    (hhi : background + 64*v ≤ 25 - 64*reserve - 64*τ) :
    1 ≤ background + 64*(scalarRound lower ζ reserve hlower hζ hreserve v).value ∧
      background + 64*(scalarRound lower ζ reserve hlower hζ hreserve v).value + 64*τ ≤ 25 := by
  have he := (scalarRound_bounds lower ζ reserve hlower hζ hreserve v hv).2.1
  obtain ⟨ha,hb⟩ := abs_le.mp he
  constructor <;> linarith

/-- The calibrated target may be an exact real spectral quantity; only the
emitted scalar is rational. -/
theorem scalarRound_tuning_real (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v : ℚ) (target : ℝ) (hv : lower ≤ v)
    (hcal : |(v:ℝ)⁻¹-target| ≤ (ζ:ℝ)^2/2) :
    |((scalarRound lower ζ reserve hlower hζ hreserve v).value:ℝ)⁻¹-target| ≤ (ζ:ℝ)^2 := by
  have hq := (scalarRound_bounds lower ζ reserve hlower hζ hreserve v hv).2.2
  have hr : |((scalarRound lower ζ reserve hlower hζ hreserve v).value:ℝ)⁻¹-(v:ℝ)⁻¹| ≤ (ζ:ℝ)^2/2 := by
    exact_mod_cast hq
  have ht := abs_sub_le ((scalarRound lower ζ reserve hlower hζ hreserve v).value:ℝ)⁻¹ (v:ℝ)⁻¹ target
  linarith

end Maxwell.Realization
