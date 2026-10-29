import Maxwell.Spectral.PrimitiveYee
import Maxwell.Spectral.CurlNorm
import Maxwell.Spectral.YeeTaylorConvolution
import Maxwell.Spectral.ScalarBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Centered-gauge Taylor series of the actual primitive Yee stencil. -/
namespace Maxwell.Spectral.YeeTaylor
noncomputable section
open Matrix
open Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee
open scoped Classical Matrix.Norms.L2Operator

local instance : Nonempty Cell := ⟨(0, 0, 0)⟩

/-- Uniform interior phase increment per half edge in Cartesian reciprocal
coordinates, whose conventional period is twenty physical cells. -/
def theta : ℝ := Real.pi / 20

def radius (q : Momentum) : ℝ := ‖WithLp.toLp 2 q‖

theorem theta_pos : 0 < theta := div_pos Real.pi_pos (by norm_num)

/-- The true unitary primitive-cell shift, acting on all 2000 cells. -/
theorem shift_mulVec (k : Momentum) (j : Direction) (v : Cell → ℂ) (p : Cell) :
    (PrimitiveYee.shift k j *ᵥ v) p = PrimitiveYee.boundaryPhase k j p * v (PrimitiveYee.forwardCell j p) := by
  simp [PrimitiveYee.shift, Matrix.mulVec, dotProduct, ite_mul]

theorem extend_shift (k : Momentum) (j : Direction) (v : Cell → ℂ) (r : RawCell) :
    extend k (PrimitiveYee.shift k j *ᵥ v) r = extend k v (r + rawUnit j) := by
  let p := reduceCell r
  let n := reduceTranslation r
  have hr : r = reconstruct p n := (reconstruct_reduce r).symm
  have hs : reconstruct p n + rawUnit j = forwardRaw j p + latticeVector n := by
    simp only [reconstruct, forwardRaw]
    abel
  rw [hr, hs, extend_translate]
  simp only [extend, reduceCell_reconstruct, reduceTranslation_reconstruct, shift_mulVec]
  rfl

/-- Primitive boundary phases preserve commutativity of the physical
translations, including crossings of the skew primitive-cell boundary. -/
theorem shift_commute (k : Momentum) (i j : Direction) :
    Commute (PrimitiveYee.shift k i) (PrimitiveYee.shift k j) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hleft := extend_shift k i (PrimitiveYee.shift k j *ᵥ v) (representative p)
  have hright := extend_shift k j (PrimitiveYee.shift k i *ᵥ v) (representative p)
  rw [extend_representative, extend_shift] at hleft hright
  rw [hleft, hright]
  congr 1
  abel

/-- Commuting primitive translations also commute with backward shifts. -/
theorem shift_commute_adjoint (k : Momentum) (i j : Direction) :
    Commute (PrimitiveYee.shift k i) (PrimitiveYee.shift k j).conjTranspose := by
  have h := (shift_commute k i j).eq
  have hL := shift_conjTranspose_mul k j
  have hR := shift_mul_conjTranspose k j
  change PrimitiveYee.shift k i * (PrimitiveYee.shift k j).conjTranspose =
    (PrimitiveYee.shift k j).conjTranspose * PrimitiveYee.shift k i
  calc
    _ = (PrimitiveYee.shift k j).conjTranspose *
        (PrimitiveYee.shift k j * PrimitiveYee.shift k i) *
          (PrimitiveYee.shift k j).conjTranspose := by rw [← mul_assoc, hL, one_mul]
    _ = (PrimitiveYee.shift k j).conjTranspose *
        (PrimitiveYee.shift k i * PrimitiveYee.shift k j) *
          (PrimitiveYee.shift k j).conjTranspose := by rw [h]
    _ = _ := by rw [mul_assoc, mul_assoc, hR, mul_one]

/-- Half-edge centered forward difference around any real base momentum. -/
def centeredDifference (k q : Momentum) (j : Direction) : Matrix Cell Cell ℂ :=
  Complex.exp (Complex.I * (theta * q j : ℝ)) • PrimitiveYee.shift k j -
    Complex.exp (-Complex.I * (theta * q j : ℝ)) • (1 : Matrix Cell Cell ℂ)

/-- Exact degree-j power-series coefficient of the centered difference. -/
def differenceCoefficient (k q : Momentum) (n : ℕ) (j : Direction) : Matrix Cell Cell ℂ :=
  ((Complex.I * (theta * q j : ℝ))^n / (n.factorial : ℂ)) • PrimitiveYee.shift k j -
    ((-Complex.I * (theta * q j : ℝ))^n / (n.factorial : ℂ)) • (1 : Matrix Cell Cell ℂ)

theorem differenceCoefficient_zero (k q : Momentum) (j : Direction) :
    differenceCoefficient k q 0 j = PrimitiveYee.difference k j := by
  simp [differenceCoefficient, difference_eq_shift_sub_one]

theorem shift_norm (k : Momentum) (j : Direction) : ‖PrimitiveYee.shift k j‖ = 1 := by
  have hunit : PrimitiveYee.shift k j ∈ Matrix.unitaryGroup Cell ℂ := by
    exact ⟨shift_conjTranspose_mul k j, shift_mul_conjTranspose k j⟩
  exact CStarRing.norm_coe_unitary ⟨_, hunit⟩

/-- The centered difference is the sum of its actual exponential series. -/
theorem differenceCoefficient_hasSum (k q : Momentum) (j : Direction) :
    HasSum (fun n => differenceCoefficient k q n j) (centeredDifference k q j) := by
  have hpos := (NormedSpace.expSeries_div_hasSum_exp
    (Complex.I * (theta * q j : ℝ))).smul_const (PrimitiveYee.shift k j)
  have hneg := (NormedSpace.expSeries_div_hasSum_exp
    (-Complex.I * (theta * q j : ℝ))).smul_const (1 : Matrix Cell Cell ℂ)
  simpa only [differenceCoefficient, centeredDifference, Complex.exp_eq_exp_ℂ] using hpos.sub hneg

/-- The sharp two-unitary norm bound for each directional coefficient. -/
theorem differenceCoefficient_norm_le (k q : Momentum) (n : ℕ) (j : Direction) :
    ‖differenceCoefficient k q n j‖ ≤
      2 * (theta * |q j|)^n / (n.factorial : ℝ) := by
  have hθ : 0 ≤ theta := theta_pos.le
  calc
    ‖differenceCoefficient k q n j‖ ≤
        ‖((Complex.I * (theta * q j : ℝ))^n / (n.factorial : ℂ)) • PrimitiveYee.shift k j‖ +
        ‖((-Complex.I * (theta * q j : ℝ))^n / (n.factorial : ℂ)) • (1 : Matrix Cell Cell ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 * (theta * |q j|)^n / (n.factorial : ℝ) := by
      simp [norm_smul, shift_norm, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
      ring

/-- The entire coefficient family consists of commuting normal matrices. -/
theorem differenceCoefficient_commute_adjoint (k q : Momentum) (n : ℕ) (i j : Direction) :
    Commute (differenceCoefficient k q n i) (differenceCoefficient k q n j).conjTranspose := by
  have h := shift_commute_adjoint k i j
  unfold differenceCoefficient
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  exact (h.smul_left _).smul_right _ |>.sub_right (Commute.one_right _ |>.smul_right _) |>.sub_left
    ((Commute.one_left _).smul_left _)

theorem theta_lt : theta < 11 / 70 := by
  have h := Real.pi_lt_d4
  dsimp [theta]
  linarith

/-- Cartesian reciprocal displacement expressed in the primitive phase
coordinates `(20,0,0),(10,10,0),(10,0,10)`. -/
def cartesianIncrement (q : Momentum) : Momentum :=
  ![2 * Real.pi * q 0, Real.pi * (q 0 + q 1), Real.pi * (q 0 + q 2)]

def dotRaw (q : Momentum) (r : RawCell) : ℝ := ∑ j, q j * (r j : ℝ)

def dotOffset (q offset : Momentum) : ℝ := ∑ j, q j * offset j

theorem dotRaw_add (q : Momentum) (r s : RawCell) :
    dotRaw q (r + s) = dotRaw q r + dotRaw q s := by
  simp [dotRaw, mul_add, Finset.sum_add_distrib]

theorem dotRaw_unit (q : Momentum) (j : Direction) : dotRaw q (rawUnit j) = q j := by
  simp [dotRaw, rawUnit, Pi.single_apply, apply_ite]

theorem cartesianIncrement_pairing (q : Momentum) (n : Translation) :
    (∑ j : Direction, cartesianIncrement q j * (n j : ℝ)) =
      2 * theta * dotRaw q (latticeVector n) := by
  simp [cartesianIncrement, dotRaw, latticeVector, theta, Fin.sum_univ_three]
  ring

def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, mul_add, Complex.exp_add]

@[simp] theorem phase_star (x : ℝ) : star (phase x) = phase (-x) := by
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  simp [phase]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_unit (x : ℝ) : star (phase x) * phase x = 1 := by
  rw [phase_star, ← phase_add, neg_add_cancel, phase_zero]

/-- Diagonal gauge at an arbitrary geometric offset inside each cell. -/
def gaugeValue (q offset : Momentum) (p : Cell) : ℂ :=
  phase (2 * theta * (dotRaw q (representative p) + dotOffset q offset))

def gauge (q offset : Momentum) : Matrix Cell Cell ℂ := Matrix.diagonal (gaugeValue q offset)

theorem gaugeValue_unit (q offset : Momentum) (p : Cell) :
    star (gaugeValue q offset p) * gaugeValue q offset p = 1 := phase_unit _

theorem character_add_momentum (k l : Momentum) (n : Translation) :
    character (k + l) n = character k n * character l n := by
  simp [character, add_mul, Finset.sum_add_distrib, mul_add, Complex.exp_add]

theorem character_cartesianIncrement (q : Momentum) (n : Translation) :
    character (cartesianIncrement q) n = phase (2 * theta * dotRaw q (latticeVector n)) := by
  have h := congrArg (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))
    (cartesianIncrement_pairing q n)
  simpa only [character, phase, Complex.ofReal_sum, Complex.ofReal_mul] using h

theorem forward_dot_identity (q : Momentum) (j : Direction) (p : Cell) :
    dotRaw q (representative (PrimitiveYee.forwardCell j p)) +
      dotRaw q (latticeVector (reduceTranslation (forwardRaw j p))) =
        dotRaw q (representative p) + q j := by
  have h := congrArg (dotRaw q) (reconstruct_reduce (forwardRaw j p))
  simpa [reconstruct, PrimitiveYee.forwardCell, forwardRaw, dotRaw_add, dotRaw_unit] using h

/-- The boundary-gauge phase and position-gauge phase combine into the
uniform full-edge phase, including skew primitive-boundary crossings. -/
theorem gauge_forward (k q offset : Momentum) (j : Direction) (p : Cell) :
    PrimitiveYee.boundaryPhase (k + cartesianIncrement q) j p * gaugeValue q offset (PrimitiveYee.forwardCell j p) =
      PrimitiveYee.boundaryPhase k j p * gaugeValue q offset p * phase (2 * theta * q j) := by
  rw [PrimitiveYee.boundaryPhase, character_add_momentum, character_cartesianIncrement]
  change (PrimitiveYee.boundaryPhase k j p * phase _) * phase _ = (PrimitiveYee.boundaryPhase k j p * phase _) * phase _
  simp only [mul_assoc, ← phase_add]
  congr 2
  have h := forward_dot_identity q j p
  linear_combination 2 * theta * h

/-- Adding half of the differentiation-axis offset centers each Yee
incidence at the midpoint between its two electric-edge samples. -/
def halfAxis (j : Direction) : Momentum := Pi.single j (1 / 2)

theorem dotOffset_add_halfAxis (q offset : Momentum) (j : Direction) :
    dotOffset q (offset + halfAxis j) = dotOffset q offset + q j / 2 := by
  simp [dotOffset, halfAxis, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite]
  ring

theorem gauge_halfAxis (q offset : Momentum) (j : Direction) (p : Cell) :
    gaugeValue q (offset + halfAxis j) p = gaugeValue q offset p * phase (theta * q j) := by
  unfold gaugeValue
  rw [dotOffset_add_halfAxis, ← phase_add]
  congr 1
  ring

theorem centeredDifference_phase (k q : Momentum) (j : Direction) :
    centeredDifference k q j = phase (theta * q j) • PrimitiveYee.shift k j -
      phase (-(theta * q j)) • (1 : Matrix Cell Cell ℂ) := by
  simp [centeredDifference, phase]

private theorem gauge_shift_entry (k q offset : Momentum) (j : Direction) (p : Cell) :
    star (gaugeValue q (offset + halfAxis j) p) *
      PrimitiveYee.boundaryPhase (k + cartesianIncrement q) j p *
        gaugeValue q offset (PrimitiveYee.forwardCell j p) =
      phase (theta * q j) * PrimitiveYee.boundaryPhase k j p := by
  rw [gauge_halfAxis, star_mul, phase_star]
  calc
    _ = phase (-(theta * q j)) * star (gaugeValue q offset p) *
        (PrimitiveYee.boundaryPhase (k + cartesianIncrement q) j p *
          gaugeValue q offset (PrimitiveYee.forwardCell j p)) := by ring
    _ = _ := by
      rw [gauge_forward]
      have hc : phase (-(theta*q j)) * phase (2*theta*q j) = phase (theta*q j) := by
        rw [← phase_add]; congr 1; ring
      calc
        _ = (phase (-(theta*q j))*phase (2*theta*q j)) * PrimitiveYee.boundaryPhase k j p *
            (star (gaugeValue q offset p)*gaugeValue q offset p) := by ring
        _ = _ := by rw [hc, gaugeValue_unit, mul_one]

private theorem gauge_identity_entry (q offset : Momentum) (j : Direction) (p : Cell) :
    star (gaugeValue q (offset + halfAxis j) p) * gaugeValue q offset p =
      phase (-(theta * q j)) := by
  rw [gauge_halfAxis, star_mul, phase_star, mul_assoc, gaugeValue_unit, mul_one]

/-- Exact centered gauge identity for each directional difference, derived
from the real primitive-cell boundary phases and geometric offsets. -/
theorem centeredDifference_gauge (k q offset : Momentum) (j : Direction) :
    (gauge q (offset + halfAxis j)).conjTranspose *
      PrimitiveYee.difference (k + cartesianIncrement q) j * gauge q offset =
        centeredDifference k q j := by
  ext p r
  simp only [gauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change star (gaugeValue q (offset + halfAxis j) p) *
    ((if r = PrimitiveYee.forwardCell j p then PrimitiveYee.boundaryPhase (k + cartesianIncrement q) j p else 0) -
      (if r = p then 1 else 0)) * gaugeValue q offset r = _
  rw [centeredDifference_phase]
  simp only [PrimitiveYee.shift, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hr : r = PrimitiveYee.forwardCell j p <;> by_cases hp : r = p
  · subst r
    simp only [ite_true, hp, mul_one]
    rw [mul_sub, sub_mul]
    have hs := gauge_shift_entry k q offset j p
    rw [hp] at hs
    rw [hs, mul_one, gauge_identity_entry]
  · subst r
    simp only [ite_true, hp, Ne.symm hp, ite_false, mul_zero, sub_zero]
    exact gauge_shift_entry k q offset j p
  · subst r
    simp only [hr, ite_false, ite_true, mul_zero, zero_sub, mul_one, mul_neg, neg_mul]
    rw [gauge_identity_entry]
  · simp [hr, hp, Ne.symm hp]

/-- Complete actual three-component centered Yee curl. -/
def centeredCurl (k q : Momentum) : Matrix Face Electric ℂ :=
  curlBlock (centeredDifference k q)

/-- Homogeneous coefficients of the full curl, including all components. -/
def curlCoefficient (k q : Momentum) (n : ℕ) : Matrix Face Electric ℂ :=
  curlBlock (differenceCoefficient k q n)

theorem curlCoefficient_zero (k q : Momentum) :
    curlCoefficient k q 0 = PrimitiveYee.curl k := by
  unfold curlCoefficient
  rw [show differenceCoefficient k q 0 = PrimitiveYee.difference k from
    funext (differenceCoefficient_zero k q)]
  rfl

theorem curlCoefficient_hasSum (k q : Momentum) :
    HasSum (curlCoefficient k q) (centeredCurl k q) := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have hd (a : Direction) := Pi.hasSum.mp
    (Pi.hasSum.mp (differenceCoefficient_hasSum k q a) i.2) j.2
  rcases i with ⟨i, p⟩
  rcases j with ⟨j, r⟩
  fin_cases i <;> fin_cases j <;>
    simp only [curlCoefficient, centeredCurl, curlBlock, Fin.reduceFinMk, Fin.isValue,
      ite_true]
  all_goals first | exact hasSum_zero | exact hd _ | exact (hd _).neg

theorem radius_nonneg (q : Momentum) : 0 ≤ radius q := norm_nonneg _

theorem radius_sq (q : Momentum) : radius q ^ 2 = ∑ j, (q j)^2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- For positive degree, the sum of directional powers is bounded by the
power of the Euclidean radius, without an additional factor of three. -/
theorem directional_powers_le (q : Momentum) (n : ℕ) (hn : n ≠ 0) :
    (∑ j : Direction, (|q j|^n)^2) ≤ (radius q ^ n)^2 := by
  have h01 := pow_add_pow_le (sq_nonneg (q 0)) (sq_nonneg (q 1)) hn
  have h012 := pow_add_pow_le (add_nonneg (sq_nonneg (q 0)) (sq_nonneg (q 1)))
    (sq_nonneg (q 2)) hn
  have habs (j : Direction) : (|q j|^n)^2 = ((q j)^2)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, sq_abs]
  simp only [habs, Fin.sum_univ_three]
  have hr : (radius q^n)^2 = ((q 0)^2+(q 1)^2+(q 2)^2)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, radius_sq, Fin.sum_univ_three]
  rw [hr]
  linarith

/-- Positive Taylor degrees have the sharp curl bound `2*(θr)^n/n!`.
The directional translations and their adjoints commute by construction. -/
theorem curlCoefficient_norm_le (k q : Momentum) (n : ℕ) (hn : n ≠ 0) :
    ‖curlCoefficient k q n‖ ≤ 2 * (theta * radius q)^n / (n.factorial : ℝ) := by
  have h := curlBlock_norm_le (differenceCoefficient k q n)
    (differenceCoefficient_commute_adjoint k q n)
    (fun j => 2 * (theta * |q j|)^n / (n.factorial : ℝ)) (fun j => by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact differenceCoefficient_norm_le k q n j)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at h
  apply h.trans
  apply (Real.sqrt_le_iff).mpr
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (mul_nonneg theta_pos.le (radius_nonneg q)) n)) (Nat.cast_nonneg _)
  have hp := directional_powers_le q n hn
  have hfactor : 0 ≤ (2 * theta^n / (n.factorial : ℝ))^2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hp hfactor
  convert hmul using 1 <;>
    simp only [Fin.sum_univ_three, mul_pow, div_pow] <;> ring

/-- The zeroth curl coefficient has norm at most `2√3`. -/
theorem curlCoefficient_zero_norm_le (k q : Momentum) :
    ‖curlCoefficient k q 0‖ ≤ 2 * Real.sqrt 3 := by
  have h := curlBlock_norm_le (differenceCoefficient k q 0)
    (differenceCoefficient_commute_adjoint k q 0) (fun _ => 2) (fun j => by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      simpa using differenceCoefficient_norm_le k q 0 j)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at h
  have hs : Real.sqrt (∑ _ : Direction, (2 : ℝ)^2) = 2 * Real.sqrt 3 := by
    norm_num only [Fin.sum_univ_three, Nat.reduceAdd, Nat.reducePow]
    calc
      Real.sqrt 12 = Real.sqrt 4 * Real.sqrt 3 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
      _ = _ := by norm_num
  exact h.trans_eq hs

/-- The full Maxwell fiber in midpoint gauge; the averaged material is exactly
the actual primitive diagonal material, with the physical frequency factor. -/
def centeredFiber (material : Cell20 → ℝ) (k q : Momentum) : Matrix Electric Electric ℂ :=
  (centeredCurl k q).conjTranspose * centeredCurl k q -
    (1 / 64 : ℂ) • PrimitiveYee.mass material

/-- Actual homogeneous Maxwell coefficients. Material enters only degree zero. -/
def fiberCoefficient (material : Cell20 → ℝ) (k q : Momentum) (n : ℕ) :
    Matrix Electric Electric ℂ :=
  YeeTaylorConvolution.coefficient (curlCoefficient k q) n -
    if n = 0 then (1 / 64 : ℂ) • PrimitiveYee.mass material else 0

theorem fiberCoefficient_zero (material : Cell20 → ℝ) (k q : Momentum) :
    fiberCoefficient material k q 0 = PrimitiveYee.fiber material k := by
  simp [fiberCoefficient, YeeTaylorConvolution.coefficient, curlCoefficient_zero, PrimitiveYee.fiber, Matrix.star_eq_conjTranspose]

/-- Genuine convergence of the concrete finite primitive Maxwell Taylor series. -/
theorem fiberCoefficient_hasSum (material : Cell20 → ℝ) (k q : Momentum) :
    HasSum (fiberCoefficient material k q) (centeredFiber material k q) := by
  have hc := YeeTaylorConvolution.coefficient_hasSum_of_bound
    (curlCoefficient k q) (centeredCurl k q) (theta * radius q)
    (curlCoefficient_hasSum k q) (fun n hn => curlCoefficient_norm_le k q n (by omega))
  have hm : HasSum (fun n : ℕ => if n = 0 then (1 / 64 : ℂ) • PrimitiveYee.mass material else 0)
      ((1 / 64 : ℂ) • PrimitiveYee.mass material) := by
    exact hasSum_ite_eq 0 _
  exact hc.sub hm

/-- The advertised paper coefficient bound is derived from the concrete Yee
stencil, its Euclidean norm, and the exact adjoint-product convolution. -/
theorem fiberCoefficient_norm_le (material : Cell20 → ℝ) (k q : Momentum)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖fiberCoefficient material k q n‖ ≤
      (4 * 2^n + 6) * (11 / 70 : ℝ)^n * radius q^n / (n.factorial : ℝ) := by
  have h := YeeTaylorConvolution.norm_coefficient_le (curlCoefficient k q)
    (theta * radius q) (mul_nonneg theta_pos.le (radius_nonneg q))
    (curlCoefficient_zero_norm_le k q)
    (fun j hj => curlCoefficient_norm_le k q j (by omega)) n hn
  simp only [fiberCoefficient, show n ≠ 0 by omega, ite_false, sub_zero]
  refine h.trans ?_
  rw [mul_pow, mul_assoc (4 * 2^n + 6)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ theta_pos.le theta_lt.le n) (pow_nonneg (radius_nonneg q) n)

/-- Geometric face midpoint offsets; electric edges use `halfAxis`. -/
def faceOffset (j : Direction) : Momentum :=
  ![halfAxis 1 + halfAxis 2, halfAxis 2 + halfAxis 0, halfAxis 0 + halfAxis 1] j

def electricGauge (q : Momentum) : Matrix Electric Electric ℂ :=
  Matrix.diagonal fun e => gaugeValue q (halfAxis e.1) e.2

def faceGauge (q : Momentum) : Matrix Face Face ℂ :=
  Matrix.diagonal fun f => gaugeValue q (faceOffset f.1) f.2

theorem electricGauge_unitary (q : Momentum) :
    (electricGauge q).conjTranspose * electricGauge q = 1 ∧
      electricGauge q * (electricGauge q).conjTranspose = 1 := by
  constructor <;>
    simp only [electricGauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  all_goals
    ext i j
    simp only [Matrix.diagonal_apply, Pi.star_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      first | exact gaugeValue_unit _ _ _ | exact (mul_comm _ _).trans (gaugeValue_unit _ _ _)
    · simp [hij]

theorem faceGauge_unitary (q : Momentum) :
    (faceGauge q).conjTranspose * faceGauge q = 1 ∧
      faceGauge q * (faceGauge q).conjTranspose = 1 := by
  constructor <;>
    simp only [faceGauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  all_goals
    ext i j
    simp only [Matrix.diagonal_apply, Pi.star_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      first | exact gaugeValue_unit _ _ _ | exact (mul_comm _ _).trans (gaugeValue_unit _ _ _)
    · simp [hij]

/-- The centered curl is unitarily gauge equivalent to the actual primitive
boundary-phase Yee curl at the displaced physical momentum. -/
theorem centeredCurl_gauge (k q : Momentum) :
    (faceGauge q).conjTranspose * PrimitiveYee.curl (k + cartesianIncrement q) * electricGauge q =
      centeredCurl k q := by
  have hd (offset : Momentum) (a : Direction) (p r : Cell) :=
    congrArg (fun M : Matrix Cell Cell ℂ => M p r) (centeredDifference_gauge k q offset a)
  simp only [gauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply] at hd
  ext ⟨i, p⟩ ⟨j, r⟩
  simp only [faceGauge, electricGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveYee.curl, centeredCurl, curlBlock, faceOffset, Pi.star_apply]
  · exact hd (halfAxis 1) 2 p r
  · simpa only [add_comm, starRingEnd_apply] using hd (halfAxis 2) 1 p r
  · simpa only [add_comm, starRingEnd_apply] using hd (halfAxis 0) 2 p r
  · exact hd (halfAxis 2) 0 p r
  · exact hd (halfAxis 0) 1 p r
  · simpa only [add_comm, starRingEnd_apply] using hd (halfAxis 1) 0 p r

/-- A midpoint phase gauge leaves every actual diagonal averaged material
unchanged, independently of the material's symmetry. -/
theorem mass_gauge (material : Cell20 → ℝ) (q : Momentum) :
    (electricGauge q).conjTranspose * PrimitiveYee.mass material * electricGauge q =
      PrimitiveYee.mass material := by
  ext i j
  simp only [electricGauge, PrimitiveYee.mass, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs
  · have h := gaugeValue_unit q (halfAxis i.1) i.2
    change star (gaugeValue q (halfAxis i.1) i.2) * _ * gaugeValue q (halfAxis i.1) i.2 = _
    calc
      _ = (star (gaugeValue q (halfAxis i.1) i.2) * gaugeValue q (halfAxis i.1) i.2) *
          (PrimitiveYee.edgeAverage material i : ℂ) := by ring
      _ = _ := by rw [h, one_mul]
  · rfl

/-- The Taylor-summed fiber is exactly the midpoint gauge of the physical
primitive Maxwell matrix, with its actual scalar-cell material averaging. -/
theorem centeredFiber_gauge (material : Cell20 → ℝ) (k q : Momentum) :
    (electricGauge q).conjTranspose *
      PrimitiveYee.fiber material (k + cartesianIncrement q) * electricGauge q =
        centeredFiber material k q := by
  rw [centeredFiber, ← centeredCurl_gauge, PrimitiveYee.fiber]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [mass_gauge]
  congr 1
  have hF := (faceGauge_unitary q).2
  calc
    _ = (electricGauge q).conjTranspose *
        (PrimitiveYee.curl (k + cartesianIncrement q)).conjTranspose *
        (faceGauge q * (faceGauge q).conjTranspose) *
        PrimitiveYee.curl (k + cartesianIncrement q) * electricGauge q := by rw [hF]; simp [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- The same exact Taylor coefficients after a fixed spectral shift. -/
def shiftedFiberCoefficient (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) (n : ℕ) :
    Matrix Electric Electric ℂ :=
  fiberCoefficient material k q n - if n = 0 then (E : ℂ) • 1 else 0

theorem shiftedFiberCoefficient_zero (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    shiftedFiberCoefficient material k q E 0 = PrimitiveYee.fiber material k - (E : ℂ) • 1 := by
  simp [shiftedFiberCoefficient, fiberCoefficient_zero]

theorem shiftedFiberCoefficient_hasSum (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    HasSum (shiftedFiberCoefficient material k q E)
      (centeredFiber material k q - (E : ℂ) • 1) := by
  exact (fiberCoefficient_hasSum material k q).sub (hasSum_ite_eq 0 _)

theorem shiftedFiberCoefficient_norm_le (material : Cell20 → ℝ) (k q : Momentum)
    (E : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖shiftedFiberCoefficient material k q E n‖ ≤
      taylorCoefficientMajorant n * radius q^n := by
  simp only [shiftedFiberCoefficient, show n ≠ 0 by omega, ite_false, sub_zero]
  convert fiberCoefficient_norm_le material k q n hn using 1
  unfold taylorCoefficientMajorant
  ring

/-- Continuous Euclidean identification used to feed the concrete matrix
Taylor series directly to the operator remainder theorems. -/
def euclideanMap : Matrix Electric Electric ℂ →L[ℂ]
    (EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric) :=
  (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

def shiftedOperatorCoefficient (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) (n : ℕ) :
    EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  euclideanMap (shiftedFiberCoefficient material k q E n)

def shiftedCenteredOperator (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  euclideanMap (centeredFiber material k q - (E : ℂ) • 1)

theorem shiftedOperatorCoefficient_hasSum (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    HasSum (shiftedOperatorCoefficient material k q E) (shiftedCenteredOperator material k q E) :=
  (shiftedFiberCoefficient_hasSum material k q E).mapL euclideanMap

theorem shiftedOperatorCoefficient_norm_le (material : Cell20 → ℝ) (k q : Momentum)
    (E : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖shiftedOperatorCoefficient material k q E n‖ ≤
      taylorCoefficientMajorant n * radius q^n := by
  change ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (shiftedFiberCoefficient material k q E n)‖ ≤ _
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact shiftedFiberCoefficient_norm_le material k q E n hn

end
end Maxwell.Spectral.YeeTaylor
