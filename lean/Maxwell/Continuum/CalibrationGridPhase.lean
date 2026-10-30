import Maxwell.Continuum.PhaseEvaluation
import Maxwell.Continuum.PeriodicSamplingProduct

/-! Rational evaluation of exact finite Fourier characters. Reducing
the dot product modulo the grid size keeps the elementary argument in
one turn, independently of the integer Fourier frequency. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate

variable (N : ℕ) [NeZero N]

def gridTurn (j : ZMod N) : ℚ := (j.val : ℚ)/N

theorem gridTurn_bound (j : ZMod N) : |gridTurn N j| ≤ 1 := by
  have hn : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [abs_of_nonneg (by unfold gridTurn; positivity : 0 ≤ gridTurn N j)]
  exact (div_le_one hn).mpr (by exact_mod_cast (ZMod.val_lt j).le)

def gridCharacterApprox (P : ℕ) (j : ZMod N) : ComplexRectangle :=
  ⟨cosTurnApprox (gridTurn N j) 1 P,sinTurnApprox (gridTurn N j) 1 P⟩

theorem stdCharacter_phase (j : ZMod N) :
    ZMod.stdAddChar j = Complex.exp (((2*Real.pi*(gridTurn N j : ℝ) : ℝ) : ℂ)*Complex.I) := by
  have hp := PeriodicSampling.phase_grid N 1 j
  norm_num only [Int.cast_one,one_mul] at hp
  rw [← hp,PeriodicSampling.phase]
  congr 1
  simp only [gridTurn,Rat.cast_div,Rat.cast_natCast]
  push_cast
  ring

theorem gridCharacterApprox_contains (P : ℕ) (j : ZMod N) :
    (gridCharacterApprox N P j).Contains (ZMod.stdAddChar j) := by
  rw [stdCharacter_phase]
  constructor
  · change (cosTurnApprox (gridTurn N j) 1 P).Contains _
    rw [Complex.exp_ofReal_mul_I_re]
    exact cosTurnApprox_contains _ _ _ (gridTurn_bound N j)
  · change (sinTurnApprox (gridTurn N j) 1 P).Contains _
    rw [Complex.exp_ofReal_mul_I_im]
    exact sinTurnApprox_contains _ _ _ (gridTurn_bound N j)

def rectangleCenter (a : ComplexRectangle) : ℂ := (a.re.center : ℂ)+(a.im.center : ℂ)*Complex.I

theorem rectangle_center_error {a : ComplexRectangle} {z : ℂ} (hz : a.Contains z) :
    ‖z-rectangleCenter a‖ ≤ (a.re.radius : ℝ)+(a.im.radius : ℝ) := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simpa only [rectangleCenter,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ratCast_re,Complex.ratCast_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] using
      add_le_add hz.1 hz.2

theorem gridCharacterApprox_error (P : ℕ) (j : ZMod N) :
    ‖ZMod.stdAddChar j-rectangleCenter (gridCharacterApprox N P j)‖ ≤ 2*(1/2 : ℝ)^P := by
  have h := rectangle_center_error (gridCharacterApprox_contains N P j)
  simp only [gridCharacterApprox,cosTurnApprox_radius,sinTurnApprox_radius] at h
  push_cast at h
  simpa only [gridCharacterApprox,two_mul] using h

variable {ι : Type*} [Fintype ι]

def productCharacterApprox (P : ℕ) (a j : ι → ZMod N) : ComplexRectangle :=
  gridCharacterApprox N P (∑ i, a i*j i)

theorem product_character_sum (a j : ι → ZMod N) :
    PeriodicSampling.Product.character N a j = ZMod.stdAddChar (∑ i, a i*j i) := by
  classical
  have hs (s : Finset ι) : (∏ i ∈ s,ZMod.stdAddChar (a i*j i)) =
      ZMod.stdAddChar (∑ i ∈ s,a i*j i) := by
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert i s hi ih => simp [hi,AddChar.map_add_eq_mul,ih]
  exact hs Finset.univ

theorem productCharacterApprox_contains (P : ℕ) (a j : ι → ZMod N) :
    (productCharacterApprox N P a j).Contains (PeriodicSampling.Product.character N a j) := by
  rw [product_character_sum]
  exact gridCharacterApprox_contains N P _

theorem productCharacterApprox_error (P : ℕ) (a j : ι → ZMod N) :
    ‖PeriodicSampling.Product.character N a j-
      rectangleCenter (productCharacterApprox N P a j)‖ ≤ 2*(1/2 : ℝ)^P := by
  rw [product_character_sum]
  exact gridCharacterApprox_error N P _

#print axioms gridCharacterApprox_contains
#print axioms productCharacterApprox_error

end Maxwell.Continuum.Calibration
