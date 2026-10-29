import Maxwell.Composition.SelectedCoefficientWidths
import Maxwell.Codec.RationalShort

/-! Logarithmic widths of the actual random midpoint and residual tolerance. -/
noncomputable section
namespace Maxwell.Composition.SelectedGridWidths
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Composition.SelectedSpacingBounds Maxwell.Composition.SelectedDimensionBounds
open Maxwell.Composition.SelectedCoefficientWidths
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

theorem inverse_power_short (b : ℕ) :
    Source.ShortRational ((b+2:ℕ):ℝ) ((2:ℚ)^b)⁻¹ := by
  let q : Codec.RationalPair := ⟨1,2^b,by positivity⟩
  have he : q.value = ((2:ℚ)^b)⁻¹ := by simp [q,Codec.RationalPair.value]
  rw [←he]
  apply Codec.RationalPair.value_short
  constructor
  · change signedBitLength (1:ℤ)≤b+2
    norm_num [signedBitLength,unsignedBitLength]
  · change unsignedBitLength (2^b)≤b+2
    rw [Dyadic.denominator_bitLength]
    omega

theorem unit_short (m e : ℕ) (budget : ℚ) (hbudget : 0 < budget)
    (hbound : (precisionUnit budget hbudget)⁻¹ ≤ (m:ℚ)^e) :
    Source.ShortRational (((e+2)*unsignedBitLength (2+m):ℕ):ℝ) (precisionUnit budget hbudget) := by
  have hi : budget⁻¹ ≤ (m:ℚ)^e :=
    ((inv_le_inv₀ hbudget (precisionUnit_pos budget hbudget)).mpr
      (precisionUnit_le budget hbudget)).trans hbound
  have hp := precisionBits_le_clog budget hbudget m 0 e
    (by simpa only [pow_zero,one_mul] using hi)
  have hb := clog_le_inputBitLength m
  have hpos := inputBitLength_pos m
  have hs := inverse_power_short (precisionBits budget hbudget)
  rw [show precisionUnit budget hbudget = ((2:ℚ)^precisionBits budget hbudget)⁻¹ by simp [precisionUnit]]
  apply hs.mono
  exact_mod_cast (show precisionBits budget hbudget+2≤(e+2)*unsignedBitLength (2+m) by
    nlinarith [Nat.mul_le_mul_left e hb])

def gridExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  16+2*(max 1 (dimensionExponent p R)+1)
def randomCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ := gridExponent p R+1
def midpointCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  2*randomCoefficient p R+detuningExponent p R+9
def toleranceCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ := toleranceExponent p R+2

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm
local notation "B" => unsignedBitLength (2+S.nnz)

theorem grid_size_bound (m N n : ℕ) (hm2 : 2≤m) (hN : (N:ℚ)≤(m:ℚ)^n) :
    (16*(m+N)^2).size ≤ (16+2*(max 1 n+1)+1)*unsignedBitLength (2+m) := by
  have hsum := add_bound m 1 n hm2 (x:=(m:ℚ)) (by simp) hN
  have hsquare := pow_bound m (max 1 n+1) 2 (by positivity) hsum
  have hprod := mul_bound m 16 ((max 1 n+1)*2)
    (constant_bound m 16 hm2) hsquare (by positivity)
  have hnat : 16*(m+N)^2 ≤ m^(16+2*(max 1 n+1)) := by
    have hcast : ((16*(m+N)^2:ℕ):ℚ) ≤ (m:ℚ)^(16+(max 1 n+1)*2) := by
      push_cast
      exact hprod
    rw [Nat.mul_comm (max 1 n+1) 2] at hcast
    exact_mod_cast hcast
  have hp : m^(16+2*(max 1 n+1)) ≤ 2^((16+2*(max 1 n+1))*Nat.clog 2 m) := by
    have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1<2) m) (16+2*(max 1 n+1))
    simpa only [←pow_mul,Nat.mul_comm] using h
  have hsize : (16*(m+N)^2).size ≤ (16+2*(max 1 n+1))*Nat.clog 2 m+1 := by
    apply Nat.size_le.mpr
    apply (hnat.trans hp).trans_lt
    rw [pow_succ]
    have hz : 0<2^((16+2*(max 1 n+1))*Nat.clog 2 m) := by positivity
    omega
  have hb := clog_le_inputBitLength m
  have hz := inputBitLength_pos m
  nlinarith [Nat.mul_le_mul_left (16+2*(max 1 n+1)) hb]

theorem random_bits (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).randomBits R ≤ randomCoefficient p R*B :=
  grid_size_bound S.nnz (Fintype.card ((I).box R).Edge) (dimensionExponent p R) hm2
    (dimension_bound p S hm R hm2 hunit)

theorem detuning_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    Source.ShortRational (((detuningExponent p R+2)*B:ℕ):ℝ)
      (PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R)) :=
  unit_short S.nnz (detuningExponent p R) _ _ (detuning_bound p S hm R hm2 hunit)

theorem tolerance_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    Source.ShortRational ((toleranceCoefficient p R*B:ℕ):ℝ) ((I).residualTolerance R) :=
  unit_short S.nnz (toleranceExponent p R) _ _
    (R.physical.constants.residualUnit_inverse_literal (I).epsilon ((I).backgroundBudget R)
      (I).epsilon_pos ((I).backgroundBudget_pos R) S.nnz _ _ hm2
      (error_inverse_bound p S hm hm2 hunit) (background_bound p S hm R hm2 hunit))

theorem midpoint_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (j : Fin (2^(I).randomBits R)) :
    Source.ShortRational ((midpointCoefficient p R*B:ℕ):ℝ)
      (PhysicalMaterial.sigma R.physical ((I).zeta R) ((I).zeta_pos R) _ j) := by
  have hj : Source.ShortRational (((I).randomBits R+1:ℕ):ℝ) (j.val:ℚ) := by
    constructor
    · simp only [Rat.num_natCast,signedBitLength,Int.natAbs_natCast]
      have hs : j.val.size≤(I).randomBits R := Nat.size_le.mpr j.isLt
      rw [Codec.unsignedBitLength_eq_size]
      exact_mod_cast (show j.val.size+1≤(I).randomBits R+1 by omega)
    · simp only [Rat.den_natCast]
      norm_num [unsignedBitLength]
  have hhalf : Source.ShortRational (3:ℝ) (1/2:ℚ) := by
    norm_num [Source.ShortRational,signedBitLength,unsignedBitLength]
  have ht := detuning_short p S hm R hm2 hunit
  have h := ((hj.add hhalf).mul ht).mul (inverse_power_short ((I).randomBits R))
  have he : PhysicalMaterial.sigma R.physical ((I).zeta R) ((I).zeta_pos R) _ j =
      ((j.val:ℚ)+1/2)*PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R)*
        ((2:ℚ)^(I).randomBits R)⁻¹ := by
    simp only [PhysicalMaterial.sigma,Probability.rationalMidpoint,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv]
  rw [he]
  apply h.mono
  have hr := random_bits p S hm R hm2 hunit
  have hb := inputBitLength_pos S.nnz
  unfold midpointCoefficient
  exact_mod_cast (show (I).randomBits R+1+3+1+(detuningExponent p R+2)*B+
      ((I).randomBits R+2)≤(2*randomCoefficient p R+detuningExponent p R+9)*B by nlinarith)

end Maxwell.Composition.SelectedGridWidths
