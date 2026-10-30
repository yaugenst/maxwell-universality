import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Continuum.CalibrationCompactFrequency

/-! Actual support and rescaled-frequency bounds of the finite power
algorithm. Multiplication by the physical well scale cancels the
supercell factor in each radial convolution degree. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open Supercell MasterConstants

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] MasterConstants.exponent MasterConstants.Cs

def radialBudget (e : ℕ) : ℕ := 4*(2 : ℕ)^(3*e)

attribute [local irreducible] size scale precision rootBits iterations inverseSteps rootDegree radialBudget

theorem mode_radius (L r N : ℕ) (z : ℚ) :
    (mode L r N z).radius=
      3*size L r N+rootDegree (scale L r N) (precision L r N) (rootBits L r N)+
      iterations N*(2*rootDegree (scale L r N) (precision L r N) (rootBits L r N)+
        size L r N*(inverseSteps L r N+6)) := by
  have hnorm (P : ℕ) (v : FourierData) : (FourierData.normalizeData P v).radius=v.radius := rfl
  have hroot (s : ℚ) (P ell : ℕ) (v : FourierData) :
      (FourierData.rootApply s P ell v).radius=v.radius+rootDegree s P ell := rfl
  have hseed (M : ℕ) [NeZero M] (P : ℕ) : (finiteSeed M P).radius=3*M := by
    change M*(1+2)=3*M
    omega
  simp only [mode,hnorm,rawMode,FourierData.iterate_radius,seed,rawSeed,hroot,hseed]

theorem radialBudget_real (e : ℕ) : (radialBudget e : ℝ)=4*((2 : ℝ)^e)^3 := by
  simp only [radialBudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← pow_mul,Nat.mul_comm e 3]

theorem rootDegree_weighted {L : ℕ} (hL : 0<L) (r N : ℕ) :
    L*rootDegree (scale L r N) (precision L r N) (rootBits L r N)≤
      radialBudget exponent*size L r N*(precision L r N+rootBits L r N+2)^2 := by
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  have hr := mul_le_mul_of_nonneg_left
    (rootDegree_upper (scale L r N) (scale_lower hL r N) (precision L r N) (rootBits L r N)) hLr.le
  have he : (L : ℝ)*(2*Cs^3*(scale L r N : ℝ)*
      ((precision L r N+rootBits L r N+2 : ℕ) : ℝ)^2)=
      (radialBudget exponent : ℝ)*(size L r N : ℝ)*
        ((precision L r N+rootBits L r N+2 : ℕ) : ℝ)^2 := by
    rw [radialBudget_real]
    simp only [Cs,scale,torusScale,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
    field_simp
    ring
  rw [he] at hr
  exact_mod_cast hr

def modeFrequencyBudget (L r N : ℕ) : ℕ :=
  2*L+(2*iterations N+1)*radialBudget exponent*(precision L r N+rootBits L r N+2)^2+
    iterations N*L*(inverseSteps L r N+6)

theorem modeFrequencyBudget_spec {L : ℕ} (hL : 0<L) (r N : ℕ) (z : ℚ) :
    L*(mode L r N z).radius≤2*size L r N*modeFrequencyBudget L r N := by
  have hD := rootDegree_weighted hL r N
  have hn := Nat.mul_le_mul_left (2*iterations N+1) hD
  rw [mode_radius]
  unfold modeFrequencyBudget
  calc
    _ = 3*L*size L r N+(2*iterations N+1)*(L*rootDegree (scale L r N)
        (precision L r N) (rootBits L r N))+iterations N*L*size L r N*(inverseSteps L r N+6) := by ring
    _ ≤ 3*L*size L r N+(2*iterations N+1)*(radialBudget exponent*size L r N*
        (precision L r N+rootBits L r N+2)^2)+iterations N*L*size L r N*(inverseSteps L r N+6) :=
      Nat.add_le_add_right (Nat.add_le_add_left hn _) _
    _ ≤ 2*size L r N*(2*L+(2*iterations N+1)*radialBudget exponent*
        (precision L r N+rootBits L r N+2)^2+iterations N*L*(inverseSteps L r N+6)) := by
      have h0 := Nat.zero_le (L*size L r N)
      have h1 := Nat.zero_le ((2*iterations N+1)*radialBudget exponent*size L r N*
        (precision L r N+rootBits L r N+2)^2)
      have h2 := Nat.zero_le (iterations N*L*size L r N*(inverseSteps L r N+6))
      nlinarith only [h0,h1,h2]

theorem mode_computed_frequency {L : ℕ} (hL : 0<L) (r N : ℕ) (z : ℚ) :
    templateFrequencyBound (size L r N) (L : ℚ) (mode L r N z).radius≤
      modeFrequencyBudget L r N := by
  apply templateFrequencyBound_le
  rw [abs_of_nonneg (Nat.cast_nonneg L)]
  exact_mod_cast modeFrequencyBudget_spec hL r N z

def supportResourceCoefficient (C : ℕ) : ℕ :=
  3+(1+2*C)*radialBudget exponent*(2*C+2)^2+C*(C+6)

def frequencyResourceCoefficient (C : ℕ) : ℕ :=
  2*C+(2*C+1)*radialBudget exponent*(2*C+2)^2+C^2*(C+6)

theorem mode_support_bound {L : ℕ} (hL : 0<L) (r N C ℓ : ℕ) (z : ℚ) (hℓ : 0<ℓ)
    (hW : precision L r N≤C*ℓ) (hB : rootBits L r N≤C*ℓ)
    (hK : inverseSteps L r N≤C*ℓ) (hn : iterations N≤C*ℓ) :
    (mode L r N z).radius≤supportResourceCoefficient C*size L r N*ℓ^3 := by
  have hD := rootDegree_weighted hL r N
  have hD' : rootDegree (scale L r N) (precision L r N) (rootBits L r N)≤
      radialBudget exponent*size L r N*(precision L r N+rootBits L r N+2)^2 := by
    exact (Nat.le_mul_of_pos_left _ hL).trans hD
  have hA : precision L r N+rootBits L r N+2≤(2*C+2)*ℓ := by nlinarith only [hW,hB,hℓ]
  have hd : rootDegree (scale L r N) (precision L r N) (rootBits L r N)≤
      radialBudget exponent*size L r N*(2*C+2)^2*ℓ^2 := by
    apply hD'.trans
    convert Nat.mul_le_mul_left (radialBudget exponent*size L r N) (Nat.pow_le_pow_left hA 2) using 1
    ring
  have hK' : inverseSteps L r N+6≤(C+6)*ℓ := by nlinarith only [hK,hℓ]
  have hℓ23 : ℓ^2≤ℓ^3 := Nat.pow_le_pow_right hℓ (by decide)
  have h13 : 1≤ℓ^3 := one_le_pow₀ (by omega)
  rw [mode_radius]
  calc
    _ ≤ 3*size L r N+radialBudget exponent*size L r N*(2*C+2)^2*ℓ^2+
        C*ℓ*(2*(radialBudget exponent*size L r N*(2*C+2)^2*ℓ^2)+size L r N*((C+6)*ℓ)) := by
      gcongr
    _ ≤ supportResourceCoefficient C*size L r N*ℓ^3 := by
      unfold supportResourceCoefficient
      have h0 := Nat.mul_le_mul_left (3*size L r N) h13
      have h1 := Nat.mul_le_mul_left (radialBudget exponent*size L r N*(2*C+2)^2) hℓ23
      have h2 := Nat.mul_le_mul_left (C*size L r N*(C+6)) hℓ23
      nlinarith only [h0,h1,h2]

theorem mode_frequency_bound {L : ℕ} (hL : 0<L) (r N C ℓ : ℕ) (z : ℚ) (hℓ : 0<ℓ)
    (hLsize : L≤C*ℓ^6) (hW : precision L r N≤C*ℓ) (hB : rootBits L r N≤C*ℓ)
    (hK : inverseSteps L r N≤C*ℓ) (hn : iterations N≤C*ℓ) :
    templateFrequencyBound (size L r N) (L : ℚ) (mode L r N z).radius≤
      frequencyResourceCoefficient C*ℓ^8 := by
  apply (mode_computed_frequency hL r N z).trans
  have hA : precision L r N+rootBits L r N+2≤(2*C+2)*ℓ := by nlinarith only [hW,hB,hℓ]
  have hi : 2*iterations N+1≤(2*C+1)*ℓ := by nlinarith only [hn,hℓ]
  have hK' : inverseSteps L r N+6≤(C+6)*ℓ := by nlinarith only [hK,hℓ]
  have h6 : ℓ^6≤ℓ^8 := Nat.pow_le_pow_right hℓ (by decide)
  have h3 : ℓ^3≤ℓ^8 := Nat.pow_le_pow_right hℓ (by decide)
  unfold modeFrequencyBudget
  calc
    _ ≤ 2*(C*ℓ^6)+((2*C+1)*ℓ)*radialBudget exponent*((2*C+2)*ℓ)^2+
        (C*ℓ)*(C*ℓ^6)*((C+6)*ℓ) := by gcongr
    _ ≤ frequencyResourceCoefficient C*ℓ^8 := by
      unfold frequencyResourceCoefficient
      have ha := Nat.mul_le_mul_left (2*C) h6
      have hb := Nat.mul_le_mul_left ((2*C+1)*radialBudget exponent*(2*C+2)^2) h3
      nlinarith only [ha,hb]

#print axioms mode_radius
#print axioms rootDegree_weighted
#print axioms mode_frequency_bound
#print axioms mode_support_bound

end Maxwell.Continuum.Calibration.FiniteAlgorithm
