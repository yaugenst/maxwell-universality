import Maxwell.Continuum.ParameterSpacing

/-! The actual first successful doubling search for the five continuum
spacing tests, with a proved finite search bound on every positive input. -/

namespace Maxwell.Continuum.Parameters

/-- Integer logarithms bound the rational inverse budget; no real logarithm
is evaluated by the encoder. -/
def rationalUpperBits (x : ℚ) : ℕ := Nat.clog 2 ⌈x⌉₊

theorem rationalUpperBits_spec (x : ℚ) : x ≤ (2 : ℚ)^rationalUpperBits x := by
  apply (Nat.le_ceil x).trans
  exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈x⌉₊

def spacingWitness (e L : ℕ) (K ε : ℚ) (hε : 0 < ε) : ℕ :=
  spacingThreshold e (Nat.clog 2 L) (rationalUpperBits K) (Realization.precisionBits ε hε)

theorem spacingWitness_spec {e L d : ℕ} {K ε : ℚ} (hK : 0 < K) (hε : 0 < ε)
    (hd : spacingWitness e L K ε hε ≤ d) : SpacingTest e L K ε d := by
  apply spacingThreshold_spec (Nat.le_pow_clog (by decide : 1 < 2) L) hK
    (rationalUpperBits_spec K) (d := d) (by
      rw [← Realization.precisionUnit_eq_pow]
      exact Realization.precisionUnit_le ε hε) hd

theorem spacingSearch_exists (e L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ k : ℕ, SpacingTest e L K ε (2^k) :=
  firstPower_eventual_exists (by decide) _ (fun _ hd => spacingWitness_spec hK hε hd)

/-- Literal implementation: start at one and double until all five rational
comparisons succeed. Its termination proof is erased from execution. -/
def selectedSpacing (e L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) : ℕ :=
  firstPower 2 (SpacingTest e L K ε) (spacingSearch_exists e L K ε hK hε)

theorem selectedSpacing_spec (e L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    SpacingTest e L K ε (selectedSpacing e L K ε hK hε) := firstPower_spec _ _ _

theorem selectedSpacing_pos (e L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    0 < selectedSpacing e L K ε hK hε := by unfold selectedSpacing firstPower; positivity

/-- Explicit overshoot bound for the actual search, expressed in arbitrary
valid binary budgets instead of assuming the stopping tests. -/
theorem selectedSpacing_lt_threshold {e L a b c : ℕ} {K ε : ℚ}
    (hK : 0 < K) (hε : 0 < ε) (hL : L ≤ 2^a) (hKb : K ≤ (2 : ℚ)^b)
    (hεc : (1/2 : ℚ)^c ≤ ε) :
    selectedSpacing e L K ε hK hε < 2*spacingThreshold e a b c := by
  have htest : SpacingTest e L K ε (2^Nat.clog 2 (spacingThreshold e a b c)) :=
    spacingThreshold_spec hL hK hKb hεc (Nat.le_pow_clog (by decide) _)
  have hle := firstPower_le_candidate (by decide : 1 ≤ 2) (SpacingTest e L K ε)
    (spacingSearch_exists e L K ε hK hε) htest
  have hpos : 0 < spacingThreshold e a b c := by
    unfold spacingThreshold
    positivity
  exact hle.trans_lt (powerCeiling_upper (by decide) hpos)

/-- The number of stored binary digits is bounded by the search witness's
integer logarithm, rather than by its magnitude. -/
theorem selectedSpacing_bits (e L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    (selectedSpacing e L K ε hK hε).bits.length ≤
      Nat.clog 2 (spacingWitness e L K ε hε)+1 := by
  have htest : SpacingTest e L K ε (2^Nat.clog 2 (spacingWitness e L K ε hε)) :=
    spacingWitness_spec hK hε (Nat.le_pow_clog (by decide) _)
  have he := firstPower_exponent_le 2 (SpacingTest e L K ε)
    (spacingSearch_exists e L K ε hK hε) htest
  rw [selectedSpacing, firstPower_binary_bits]
  omega

#print axioms spacingSearch_exists
#print axioms selectedSpacing_spec
#print axioms selectedSpacing_lt_threshold

end Maxwell.Continuum.Parameters
