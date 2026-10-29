import Maxwell.Continuum.Corner

/-! All sixteen transverse roots of the eight literal parity blocks. -/

noncomputable section
namespace Maxwell.Continuum.Corner

abbrev Parity := Bool × Bool × Bool

def sign (s : Bool) : ℝ := if s then 1 else -1

def parityCoefficients (p : Parity) : Vec :=
  ![sign p.1, 2 * sign p.2.1, 4 * sign p.2.2]

def parityBlock (p : Parity) : Mat := block (parityCoefficients p)

def parityRoot (p : Parity) (upper : Bool) : ℝ :=
  if upper then upperRoot (parityCoefficients p) else lowerRoot (parityCoefficients p)

def selectedParity : Parity := (true, false, false)
def nextParity : Parity := (false, true, false)
def lambdaStar : ℝ := (5 + 2 * Real.sqrt 19) / 6
def lambdaNext : ℝ := 1 / 2 + Real.sqrt 3

theorem parity_discriminant (p : Parity) :
    discriminant (parityCoefficients p) =
      21 - 2 * sign p.1 * sign p.2.1 - 4 * sign p.1 * sign p.2.2 -
        8 * sign p.2.1 * sign p.2.2 := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> norm_num [discriminant, parityCoefficients, sign]

theorem parity_root_formula (p : Parity) (upper : Bool) :
    parityRoot p upper = -(sign p.1 + 2 * sign p.2.1 + 4 * sign p.2.2) / 6 +
      sign upper * Real.sqrt (21 - 2 * sign p.1 * sign p.2.1 -
        4 * sign p.1 * sign p.2.2 - 8 * sign p.2.1 * sign p.2.2) / 3 := by
  cases upper <;> simp only [parityRoot, Bool.false_eq_true, ite_false, ite_true,
    upperRoot, lowerRoot]
  all_goals rw [parity_discriminant]
  all_goals simp [coefficientSum, parityCoefficients, sign]
  all_goals ring

/-- These are roots of the actual matrix characteristic polynomial. -/
theorem parity_root_isRoot (p : Parity) (upper : Bool) :
    (parityBlock p).charpoly.IsRoot (parityRoot p upper) := by
  cases upper
  · exact block_charpoly_lowerRoot _
  · exact block_charpoly_upperRoot _

/-- The extra characteristic root is exactly the normal direction. -/
theorem parity_charpoly_roots (p : Parity) (z : ℝ) :
    (parityBlock p).charpoly.IsRoot z ↔
      z = 0 ∨ z = parityRoot p true ∨ z = parityRoot p false :=
  block_charpoly_roots _ _

theorem selected_root : parityRoot selectedParity true = lambdaStar := by
  norm_num [parityRoot, upperRoot, parityCoefficients, selectedParity, sign,
    coefficientSum, discriminant, lambdaStar]
  ring

theorem sqrt_twenty_seven : Real.sqrt 27 = 3 * Real.sqrt 3 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem next_root : parityRoot nextParity true = lambdaNext := by
  norm_num [parityRoot, upperRoot, parityCoefficients, nextParity, sign,
    coefficientSum, discriminant, lambdaNext, sqrt_twenty_seven]

theorem sqrt_seven_upper : Real.sqrt 7 < 8 / 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_nonneg (7 : ℝ)]

theorem sqrt_nineteen_bounds : (4358 / 1000 : ℝ) < Real.sqrt 19 ∧ Real.sqrt 19 < 5 := by
  constructor <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19), Real.sqrt_nonneg (19 : ℝ)]

theorem sqrt_three_bounds : (17 / 10 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1733 / 1000 := by
  constructor <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]

theorem sqrt_thirty_one_upper : Real.sqrt 31 < 6 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31), Real.sqrt_nonneg (31 : ℝ)]

/-- Exact rational margins prove the ordering of all sixteen roots. -/
theorem other_root_le_next (p : Parity) (upper : Bool)
    (hother : (p, upper) ≠ (selectedParity, true)) : parityRoot p upper ≤ lambdaNext := by
  have h7 := sqrt_seven_upper
  have h19 := sqrt_nineteen_bounds.2
  have h19zero := Real.sqrt_nonneg (19 : ℝ)
  have h3 := sqrt_three_bounds.1
  have h31 := sqrt_thirty_one_upper
  have h7zero := Real.sqrt_nonneg (7 : ℝ)
  have h31zero := Real.sqrt_nonneg (31 : ℝ)
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> cases upper <;> simp [selectedParity] at hother
  all_goals norm_num [parityRoot, upperRoot, lowerRoot, parityCoefficients, sign,
    coefficientSum, discriminant, lambdaNext, sqrt_twenty_seven]
  all_goals linarith

theorem top_gap : 1 / 20 < lambdaStar - lambdaNext := by
  have h19 := sqrt_nineteen_bounds.1
  have h3 := sqrt_three_bounds.2
  dsimp [lambdaStar, lambdaNext]
  linarith

theorem other_root_gap (p : Parity) (upper : Bool)
    (hother : (p, upper) ≠ (selectedParity, true)) :
    1 / 20 < lambdaStar - parityRoot p upper := by
  have hroot := other_root_le_next p upper hother
  linarith [top_gap]

/-- The selected upper root is the unique largest among the sixteen roots. -/
theorem unique_top (p : Parity) (upper : Bool) :
    parityRoot p upper = lambdaStar ↔ (p, upper) = (selectedParity, true) := by
  constructor
  · intro heq
    by_contra hne
    have hgap := other_root_gap p upper hne
    rw [heq] at hgap
    norm_num at hgap
  · intro heq
    have hp : p = selectedParity := congrArg Prod.fst heq
    have hu : upper = true := congrArg Prod.snd heq
    rw [hp, hu, selected_root]

theorem lambdaStar_pos : 0 < lambdaStar := by
  dsimp [lambdaStar]
  positivity

theorem parity_charpoly_root_le_top (p : Parity) (z : ℝ)
    (hz : (parityBlock p).charpoly.IsRoot z) : z ≤ lambdaStar := by
  rcases (parity_charpoly_roots p z).mp hz with rfl | rfl | rfl
  · exact lambdaStar_pos.le
  · by_cases hp : p = selectedParity
    · rw [hp, selected_root]
    · have hgap := other_root_gap p true (by simpa using hp)
      linarith
  · have hgap := other_root_gap p false (by simp)
    linarith

end Maxwell.Continuum.Corner
