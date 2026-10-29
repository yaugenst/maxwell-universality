import Maxwell.Composition.SelectedSpacingBounds

/-! Logarithmic bounds for the actual terminating rational buffer search.
The trial-volume feedback is already included in this chosen buffer. -/
noncomputable section
namespace Maxwell.Composition.SelectedBufferBounds
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Composition.SelectedSpacingBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def distancePower (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  distanceBase R+distanceSlope p R+1
def extentPower (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  distancePower p R+sideExponent p
def rate (R : SelectedPlatform) : ℝ := -Real.log (R.physical.boundaryRate : ℝ)
def fixed (R : SelectedPlatform) : ℝ :=
  Buffer.fixedConstant (rate R) R.physical.rowBound R.physical.bulkGap R.physical.volumeCoefficient
def slope (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  4+6*(extentPower p R+1)+detuningExponent p R+2*zetaExponent p R
def coefficient (p : Source.Parameters) (R : SelectedPlatform) : ℝ :=
  2+(2/rate R)*(|Real.log (fixed R)|+slope p R)

theorem rate_pos (R : SelectedPlatform) : 0 < rate R := by
  exact neg_pos.mpr (Real.log_neg (by exact_mod_cast R.physical.boundaryRate_pos)
    (by exact_mod_cast R.physical.boundaryRate_lt_one))

theorem coefficient_pos (p : Source.Parameters) (R : SelectedPlatform) : 0 < coefficient p R := by
  have := rate_pos R
  unfold coefficient
  positivity

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem distance_power_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).distance R : ℚ) ≤ (S.nnz:ℚ)^distancePower p R := by
  have hd := distance_bound p S hm R hm2 hunit
  have hl : Nat.clog 2 S.nnz ≤ S.nnz := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h : (I).distance R ≤ (distanceBase R+distanceSlope p R)*S.nnz := by
    nlinarith
  have hR : ((I).distance R : ℚ) ≤ (distanceBase R+distanceSlope p R)*(S.nnz:ℚ) := by
    exact_mod_cast h
  have hb := mul_bound S.nnz (distanceBase R+distanceSlope p R) 1
    (constant_bound S.nnz _ hm2) (x := (distanceBase R+distanceSlope p R : ℕ))
    (y := S.nnz) (by simp) (by positivity)
  exact hR.trans (by simpa only [Nat.cast_add, distancePower] using hb)

theorem extent_power_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (((I).distance R*SourceRouting.side S (I).precision : ℕ) : ℚ) ≤
      (S.nnz:ℚ)^extentPower p R := by
  have hd := distance_power_bound p S hm R hm2 hunit
  have hs := SelectedLogicalBounds.side_bound p S hm hm2 hunit
  rw [PhysicalParameters.routingSide_eq] at hs
  simpa only [Nat.cast_mul, extentPower] using mul_bound _ _ _ hd hs (by positivity)

abbrev buffer := R.physical.chosenBuffer S (I).precision ((I).distance R)
  ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R)

theorem logarithmic (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (buffer p S hm R : ℝ) ≤ coefficient p R*(1+Real.log (S.nnz:ℝ)) := by
  have hmR : (1:ℝ) ≤ S.nnz := by exact_mod_cast hm
  have hm0 : (0:ℝ) < S.nnz := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (S.nnz:ℝ) := Real.log_nonneg hmR
  have hμ := rate_pos R
  have hτ := R.physical.constants.detuningWidth_pos ((I).zeta R) ((I).zeta_pos R)
  have hb := Buffer.rationalChoice_logarithmic_bound R.physical.boundaryRate
    R.physical.rowBound R.physical.bulkGap R.physical.volumeCoefficient
    (PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R)) ((I).zeta R)
    S.nnz ((I).distance R*SourceRouting.side S (I).precision)
    R.physical.boundaryRate_pos R.physical.boundaryRate_lt_one R.physical.rowBound_pos.le
    R.physical.bulkGap_pos R.physical.volumeCoefficient_nonneg hτ
    (R.physical.constants.detuningWidth_bounds _ ((I).zeta_pos R)).1
    ((I).zeta_pos R) ((I).zeta_one R)
  have hmplus : (S.nnz:ℝ)+1 ≤ (S.nnz:ℝ)^2 := by
    have hm2R : (2:ℝ) ≤ S.nnz := by exact_mod_cast hm2
    nlinarith
  have hlm := Real.log_le_log (by positivity : (0:ℝ)<(S.nnz:ℝ)+1) hmplus
  rw [Real.log_pow] at hlm
  have hs := extent_power_bound p S hm R hm2 hunit
  have hsplus := add_bound S.nnz (extentPower p R) 0 hm2 hs (y := 1) (by simp)
  simp only [max_zero] at hsplus
  have hsR : (((I).distance R*SourceRouting.side S (I).precision : ℕ):ℝ)+1 ≤
      (S.nnz:ℝ)^(extentPower p R+1) := by exact_mod_cast hsplus
  have hls := Real.log_le_log (by positivity) hsR
  rw [Real.log_pow] at hls
  have htR : (PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R) : ℝ)⁻¹ ≤
      (S.nnz:ℝ)^detuningExponent p R := by
    exact_mod_cast detuning_bound p S hm R hm2 hunit
  have hlt := Real.log_le_log (by exact_mod_cast inv_pos.mpr hτ) htR
  rw [Real.log_pow] at hlt
  have hzR : ((I).zeta R : ℝ)⁻¹ ≤ (S.nnz:ℝ)^zetaExponent p R := by
    exact_mod_cast (scales_bound p S hm R hm2 hunit).1
  have hlz := Real.log_le_log (by exact_mod_cast inv_pos.mpr ((I).zeta_pos R)) hzR
  rw [Real.log_pow] at hlz
  change (buffer p S hm R : ℝ) ≤ 2+(2/rate R)*
    (Real.log (fixed R)+2*Real.log ((S.nnz:ℝ)+1)+
      6*Real.log ((((I).distance R*SourceRouting.side S (I).precision : ℕ):ℝ)+1)+
      Real.log (1/(PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R) : ℝ))+
      2*Real.log (1/((I).zeta R : ℝ))) at hb
  simp only [one_div] at hb
  have hsum : Real.log (fixed R)+2*Real.log ((S.nnz:ℝ)+1)+
      6*Real.log ((((I).distance R*SourceRouting.side S (I).precision : ℕ):ℝ)+1)+
      Real.log ((PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R) : ℝ)⁻¹)+
      2*Real.log (((I).zeta R : ℝ)⁻¹) ≤
      |Real.log (fixed R)|+(slope p R : ℝ)*Real.log (S.nnz:ℝ) := by
    dsimp only [slope]
    push_cast
    push_cast at hls hlm
    nlinarith [le_abs_self (Real.log (fixed R))]
  have hupper := hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ)≤2/rate R)))
  have hnon : (0:ℝ) ≤ |Real.log (fixed R)| := abs_nonneg _
  unfold coefficient
  nlinarith [mul_nonneg hnon hlog,
    mul_nonneg (show (0:ℝ)≤2/rate R by positivity) (mul_nonneg hnon hlog),
    mul_nonneg (show (0:ℝ)≤2/rate R by positivity) (Nat.cast_nonneg (α := ℝ) (slope p R))]

end Maxwell.Composition.SelectedBufferBounds
