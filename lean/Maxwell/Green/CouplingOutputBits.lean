import Maxwell.Green.CalibrationOutputs
import Maxwell.Codec.Bounds

/-! Common denominators and storage bounds for the computed axial couplings. -/
namespace Maxwell.Realization

theorem selectedRound_den_dvd (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    (selectedRound budget hbudget x).value.den ∣ 2 ^ precisionBits budget hbudget := by
  have hd := Rat.den_dvd (selectedRound budget hbudget x).numerator
    ((2 : ℤ)^precisionBits budget hbudget)
  have he : Rat.divInt (selectedRound budget hbudget x).numerator
      ((2 : ℤ)^precisionBits budget hbudget) = (selectedRound budget hbudget x).value := by
    rw [Rat.divInt_eq_div, selectedRound_value]
    simp
  rw [he] at hd
  exact_mod_cast hd

end Maxwell.Realization

namespace Maxwell.Defect.SourceRounding

def outputDigits (n b : ℕ) : ℕ :=
  Realization.precisionBits (coordinateBudget n b) (coordinateBudget_pos n b)

theorem outputDigits_bound (n b : ℕ) : outputDigits n b ≤ 2*b+(n+1).size+1 :=
  (Realization.precisionBits_le_den_size _ _).trans (coordinateBudget_bits n b)

theorem roundedWeightedVector_den_dvd {n : ℕ} (W : Fin n → ℚ)
    (q : ℕ → Fin n → ℚ) (b : ℕ) (i : Fin n) :
    (roundedWeightedVector W q b i).den ∣ 2 ^ outputDigits n b :=
  Realization.selectedRound_den_dvd _ _ _

end Maxwell.Defect.SourceRounding

namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000

theorem HasDenominator.pairing {u v : SparseField} {D E : ℕ}
    (hu : HasDenominator u D) (hv : HasDenominator v E) :
    (pairing u v).den ∣ D*E := by
  induction u with
  | nil => simp [FiniteStencil.pairing]
  | cons t u ih =>
    simp only [FiniteStencil.pairing, List.map_cons, List.sum_cons]
    apply (Rat.add_den_dvd_lcm _ _).trans
    apply Nat.lcm_dvd
    · exact (Rat.mul_den_dvd t.2 (FiniteStencil.evaluate v t.1)).trans
        (Nat.mul_dvd_mul (hu t (by simp)) (hv.evaluate _))
    · exact ih (fun a ha => hu a (by simp [ha]))

theorem rationalSource_denominator {n : ℕ} (edges : Fin n → Edge) (a : Fin n → ℚ)
    (E : ℕ) (ha : ∀ i, (a i).den ∣ E) : HasDenominator (rationalSource edges a) E := by
  intro t ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  exact ha i

end Maxwell.Defect.FiniteStencil

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression
set_option maxHeartbeats 600000

def inverseCommonDenominator (P : PhysicalPlatform) : ℕ :=
  calibrationDenominator P.background.material 0 ((P.rowBound^2)⁻¹)

theorem signedCoupling_den_dvd (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (b E : ℕ)
    (ha : ∀ i, (a i).den ∣ E) :
    (P.signedCoupling a n b).den ∣ P.inverseCommonDenominator^(5*P.calibrationDegree b+3)*E^2 := by
  obtain ⟨_, h64, hmD, hz, hsD⟩ :=
    calibrationDenominator_spec P.background.material 0 ((P.rowBound^2)⁻¹)
  have hu := rationalSource_denominator (ScalarDefect.edgeEmbedding P.defect) a E ha
  have hv := rationalSource_denominator
    (translateEdge n ∘ ScalarDefect.edgeEmbedding P.defect) a E ha
  have hh := hu.pairing (hv.compactInverseAction P.rationalMaterial 0
    ((P.rowBound^2)⁻¹) h64 hmD hz hsD (P.calibrationDegree b))
  change (-pairing _ _).den ∣ _
  simp only [Rat.den_neg_eq_den]
  convert hh using 1
  unfold inverseCommonDenominator
  ring

theorem signedCoupling_bit_bound (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (b p cap : ℕ)
    (ha : ∀ i, (a i).den ∣ 2^p)
    (hcap : |P.signedCoupling a n b| ≤ (2 : ℚ)^cap) :
    Maxwell.rationalBitLength (P.signedCoupling a n b) ≤
      2*P.inverseCommonDenominator.size*(5*P.calibrationDegree b+3)+4*p+cap+3 := by
  have hD : 0 < P.inverseCommonDenominator :=
    (calibrationDenominator_spec P.background.material 0 ((P.rowBound^2)⁻¹)).1
  have hpow : P.inverseCommonDenominator^(5*P.calibrationDegree b+3)*(2^p)^2 ≤
      2^(P.inverseCommonDenominator.size*(5*P.calibrationDegree b+3)+2*p) := by
    calc
      _ ≤ (2^P.inverseCommonDenominator.size)^(5*P.calibrationDegree b+3)*(2^p)^2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
      _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
  have hh := rational_bit_bound (P.signedCoupling a n b)
    (P.inverseCommonDenominator^(5*P.calibrationDegree b+3)*(2^p)^2)
    (P.inverseCommonDenominator.size*(5*P.calibrationDegree b+3)+2*p) cap
    (by positivity) (P.signedCoupling_den_dvd a n b (2^p) ha) hpow hcap
  simp only [Maxwell.rationalBitLength, Maxwell.signedBitLength,
    Maxwell.Codec.unsignedBitLength_eq_size]
  simp only [Nat.mul_assoc] at *
  omega

theorem calibratedAxis_den_dvd (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (sourceTolerance ζ : ℚ) (d : ℕ) (j : Direction) :
    (P.calibratedAxis q sourceTolerance ζ d j).den ∣
      P.inverseCommonDenominator^(5*P.calibrationDegree
        (P.couplingPrecision (P.axialBudget ζ d))+3) *
      (2^SourceRounding.outputDigits (ScalarDefect.edges P.defect).card
        (P.calibrationDigits sourceTolerance ζ d))^2 := by
  unfold calibratedAxis
  rw [P.integerSignedCoupling_eq]
  exact P.signedCoupling_den_dvd _ _ _ _
    (SourceRounding.roundedWeightedVector_den_dvd _ q _)

theorem calibratedAxis_abs_bound (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (sourceTolerance : ℚ) (hsource : 0 < sourceTolerance)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction) :
    |P.calibratedAxis q sourceTolerance (P.spacing.zeta d) d j| ≤ P.greenConstant+1 := by
  have ha := (P.sourceCoordinates_error q hqnorm hqerror sourceTolerance
    (P.spacing.zeta d) hsource d).2
  have hh := P.signedCoupling_axial_upper d hd j _ ha
  have hz0 : 0 ≤ (P.spacing.zeta d : ℝ) :=
    (Rat.cast_nonneg (K := ℝ)).mpr (P.spacing.zeta_pos d).le
  have hz1 : (P.spacing.zeta d : ℝ) ≤ 1 := by
    have hh : P.spacing.zeta d ≤ 1 :=
      pow_le_one₀ P.spacing.r_pos.le P.spacing.r_lt_one.le
    exact_mod_cast hh
  have hC : 0 ≤ (P.greenConstant : ℝ) :=
    (Rat.cast_nonneg (K := ℝ)).mpr P.greenConstant_nonneg
  have hprod := mul_le_mul_of_nonneg_left hz1 hC
  have hsquare : (P.spacing.zeta d : ℝ)^2 ≤ 1 :=
    (pow_le_one₀ hz0 hz1)
  have hb : |(P.signedCoupling (P.sourceCoordinates q sourceTolerance (P.spacing.zeta d) d)
      ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d)) : ℝ)| ≤
      (P.greenConstant : ℝ)+1 := by linarith
  unfold calibratedAxis
  rw [P.integerSignedCoupling_eq]
  exact (Rat.cast_le (K := ℝ)).mp (by simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_one] using hb)

theorem calibratedAxis_bits (P : PhysicalPlatform)
    (q : ℕ → Fin (ScalarDefect.edges P.defect).card → ℚ)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b)-P.mode‖ ≤ (1/2 : ℝ)^b)
    (sourceTolerance : ℚ) (hsource : 0 < sourceTolerance)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction) :
    Maxwell.rationalBitLength (P.calibratedAxis q sourceTolerance (P.spacing.zeta d) d j) ≤
      2*P.inverseCommonDenominator.size*(5*P.calibrationDegree
        (P.couplingPrecision (P.axialBudget (P.spacing.zeta d) d))+3) +
      8*P.calibrationDigits sourceTolerance (P.spacing.zeta d) d +
      4*((ScalarDefect.edges P.defect).card+1).size+
      (P.greenConstant+1).num.natAbs.size+7 := by
  have hb := P.calibratedAxis_abs_bound q hqnorm hqerror sourceTolerance hsource d hd j
  have hcap : |P.calibratedAxis q sourceTolerance (P.spacing.zeta d) d j| ≤
      (2 : ℚ)^(P.greenConstant+1).num.natAbs.size :=
    hb.trans ((le_abs_self _).trans (Green.abs_le_pow_num_size _))
  unfold calibratedAxis at hcap ⊢
  rw [P.integerSignedCoupling_eq] at hcap ⊢
  have hh := P.signedCoupling_bit_bound
    (P.sourceCoordinates q sourceTolerance (P.spacing.zeta d) d) _ _
    (SourceRounding.outputDigits (ScalarDefect.edges P.defect).card
      (P.calibrationDigits sourceTolerance (P.spacing.zeta d) d))
    (P.greenConstant+1).num.natAbs.size
    (SourceRounding.roundedWeightedVector_den_dvd _ q _) hcap
  have hp := SourceRounding.outputDigits_bound (ScalarDefect.edges P.defect).card
    (P.calibrationDigits sourceTolerance (P.spacing.zeta d) d)
  omega

end Maxwell.Composition.PhysicalPlatform
