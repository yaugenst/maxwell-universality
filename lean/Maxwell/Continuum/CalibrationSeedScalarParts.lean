import Maxwell.Continuum.CalibrationSeedScalars
import Maxwell.Continuum.RationalDataflowParts

/-! Exact unreduced channels for the three seed scalars. The square-root
machine supplies both raw pairs; no canonical fraction is assumed. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open RationalDataflow

def denominatorPositive (a : ℕ) : ℕ := 8*361*a
def denominatorNegative (a : ℕ) : ℕ := 8*28*a
def denominatorBase (b : ℕ) : ℕ := 225*b
def denominatorNumerator (a b : ℕ) : ℕ := denominatorPositive b-denominatorNegative a
def componentParts (a b c d : ℕ) : Fin 3→Parts :=
  ![⟨(8*b+a)*d,0,15*b*c⟩,⟨b*d,a*d,6*b*c⟩,⟨a*d,7*b*d,10*b*c⟩]

theorem denominator_order (N a b : ℕ) (hb : 0<b)
    (radical : (a:ℚ)/b=seedRadical N) : denominatorNegative a≤denominatorPositive b := by
  have hupper : (a:ℚ)/b≤5 := by
    rw [radical]
    exact_mod_cast (seedRadical_bounds N).2
  have ha : (a:ℚ)≤5*b := (div_le_iff₀ (by exact_mod_cast hb)).mp hupper
  have haNat : a≤5*b := by exact_mod_cast ha
  unfold denominatorNegative denominatorPositive
  omega

theorem denominator_value (N a b : ℕ) (hb : 0<b)
    (radical : (a:ℚ)/b=seedRadical N) :
    (denominatorNumerator a b:ℚ)/denominatorBase b=seedDenominatorSq N := by
  have ordered := denominator_order N a b hb radical
  have hbq : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  rw [denominatorNumerator,Nat.cast_sub ordered]
  simp only [denominatorPositive,denominatorNegative,denominatorBase,seedDenominatorSq,
    Nat.cast_mul,Nat.cast_ofNat,←radical]
  field_simp

theorem componentParts_valid (a b c d : ℕ) (hb : 0<b) (hc : 0<c) (j : Fin 3) :
    (componentParts a b c d j).Valid := by
  fin_cases j <;> simp [componentParts,Parts.Valid,hb,hc]

theorem componentParts_value (N a b c d : ℕ) (hb : 0<b) (hd : 0<d)
    (radical : (a:ℚ)/b=seedRadical N) (denominator : (c:ℚ)/d=seedDenominator N)
    (j : Fin 3) : (componentParts a b c d j).value=seedComponent N j := by
  have hcq : (0:ℚ)<c := by
    have lower : (1:ℚ)≤seedDenominator N := by exact_mod_cast seedDenominator_lower N
    have hdiv : (0:ℚ)<(c:ℚ)/d := by rw [denominator];linarith only [lower]
    exact (div_pos_iff.mp hdiv).elim (fun h=>h.1) (fun h=>False.elim (by
      have : (0:ℚ)<d := by exact_mod_cast hd
      linarith only [this,h.2]))
  have hbq : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  have hdq : (d:ℚ)≠0 := by exact_mod_cast hd.ne'
  have hcne := ne_of_gt hcq
  fin_cases j <;>
    simp [componentParts,Parts.value,seedComponent,seedRaw,←radical,←denominator]
  all_goals field_simp

#print axioms componentParts_value
end Maxwell.Continuum.Calibration.SeedMachine
