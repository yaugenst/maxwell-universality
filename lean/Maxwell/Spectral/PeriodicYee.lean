import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conventional period-20 Yee Bloch fiber

Electric edges and curl faces are anchored at integer cell coordinates.
Twisting a forward difference at a period boundary implements the anchor
Bloch gauge. The mass uses the same four incident scalar cells as the paper.
This file defines the actual finite stencil; the unitary infinite-lattice
Bloch transform and the certified edge estimates remain separate theorems.
-/

namespace Maxwell.Spectral.PeriodicYee

abbrev Direction := Fin 3
abbrev Cell20 := Direction → ZMod 20
abbrev Electric20 := Direction × Cell20
abbrev Face20 := Direction × Cell20
abbrev Momentum := Direction → ℝ

noncomputable section

def unitCell (j : Direction) : Cell20 := Pi.single j 1

def forwardCell (j : Direction) (r : Cell20) : Cell20 := r + unitCell j

def boundaryPhase (k : Momentum) (j : Direction) (r : Cell20) : ℂ :=
  if r j = 19 then Complex.exp (Complex.I * (k j : ℂ)) else 1

def difference (k : Momentum) (j : Direction) : Matrix Cell20 Cell20 ℂ :=
  fun r s => (if s = forwardCell j r then boundaryPhase k j r else 0) -
    (if s = r then 1 else 0)

/-- Oriented curl: `(D_y E_z-D_z E_y, D_z E_x-D_x E_z,
D_x E_y-D_y E_x)`. -/
def curl (k : Momentum) : Matrix Face20 Electric20 ℂ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then difference k 1 i.2 j.2
    else if j.1 = 1 then -difference k 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then difference k 2 i.2 j.2
    else if j.1 = 2 then -difference k 0 i.2 j.2 else 0
  else
    if j.1 = 1 then difference k 0 i.2 j.2
    else if j.1 = 0 then -difference k 1 i.2 j.2 else 0

def transverseDirections (j : Direction) : Direction × Direction :=
  if j = 0 then (1, 2) else if j = 1 then (0, 2) else (0, 1)

def edgeAverage (material : Cell20 → ℝ) (e : Electric20) : ℝ :=
  let p := transverseDirections e.1
  (material e.2 + material (e.2 - unitCell p.1) +
    material (e.2 - unitCell p.2) +
    material (e.2 - unitCell p.1 - unitCell p.2)) / 4

def mass (material : Cell20 → ℝ) : Matrix Electric20 Electric20 ℂ :=
  Matrix.diagonal fun e => (edgeAverage material e : ℂ)

/-- Fixed h=1 and frequency omega=1/8, hence omega squared =1/64. -/
def fiber (material : Cell20 → ℝ) (k : Momentum) :
    Matrix Electric20 Electric20 ℂ :=
  (curl k).conjTranspose * curl k - (1 / 64 : ℂ) • mass material

theorem cell_count : Fintype.card Cell20 = 8000 := by
  norm_num [Cell20, Direction, Fintype.card_fun]

theorem electric_count : Fintype.card Electric20 = 24000 := by
  simp only [Electric20, Fintype.card_prod, Fintype.card_fin, cell_count]

theorem edgeAverage_constant (a : ℝ) (e : Electric20) :
    edgeAverage (fun _ => a) e = a := by
  dsimp [edgeAverage]
  ring

theorem edgeAverage_shift (material : Cell20 → ℝ) (a : ℝ) (e : Electric20) :
    edgeAverage (fun c => material c + a) e = edgeAverage material e + a := by
  dsimp [edgeAverage]
  ring

theorem edgeAverage_bounds (material : Cell20 → ℝ) (lo hi : ℝ)
    (h : ∀ c, lo ≤ material c ∧ material c ≤ hi) (e : Electric20) :
    lo ≤ edgeAverage material e ∧ edgeAverage material e ≤ hi := by
  dsimp [edgeAverage]
  have h0 := h e.2
  have h1 := h (e.2 - unitCell (transverseDirections e.1).1)
  have h2 := h (e.2 - unitCell (transverseDirections e.1).2)
  have h3 := h (e.2 - unitCell (transverseDirections e.1).1 -
    unitCell (transverseDirections e.1).2)
  constructor <;> linarith

theorem mass_hermitian (material : Cell20 → ℝ) : (mass material).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun e : Electric20 => (edgeAverage material e : ℂ)) = _
  funext e
  simp

theorem fiber_hermitian (material : Cell20 → ℝ) (k : Momentum) :
    (fiber material k).IsHermitian := by
  apply (Matrix.isHermitian_conjTranspose_mul_self (curl k)).sub
  exact (mass_hermitian material).smul (by
    change star (1 / 64 : ℂ) = _
    simp)

theorem fiber_uniform_shift (material : Cell20 → ℝ) (z : ℝ) (k : Momentum) :
    fiber (fun c => material c + 64 * z) k = fiber material k - (z : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fiber, mass, edgeAverage_shift]
    ring
  · simp [fiber, mass, hij]

theorem boundaryPhase_zero (j : Direction) (r : Cell20) :
    boundaryPhase (fun _ => 0) j r = 1 := by
  simp [boundaryPhase]

theorem boundaryPhase_continuous (j : Direction) (r : Cell20) :
    Continuous (fun k : Momentum => boundaryPhase k j r) := by
  unfold boundaryPhase
  split <;> fun_prop

theorem difference_continuous (j : Direction) :
    Continuous (fun k : Momentum => difference k j) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  unfold difference
  by_cases h : s = forwardCell j r
  · simp only [h, ite_true]
    exact (boundaryPhase_continuous j r).sub continuous_const
  · simp only [h, ite_false]
    exact continuous_const

theorem curl_continuous : Continuous curl := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h (d : Direction) : Continuous (fun k : Momentum => difference k d i.2 j.2) := by
    have hrow : Continuous (fun k : Momentum => difference k d i.2) :=
      (continuous_apply i.2).comp (difference_continuous d)
    exact (continuous_apply j.2).comp hrow
  unfold curl
  split_ifs <;> first | exact h _ | exact (h _).neg | exact continuous_const

theorem fiber_continuous (material : Cell20 → ℝ) :
    Continuous (fiber material) := by
  unfold fiber
  have h := curl_continuous
  fun_prop

theorem boundaryPhase_time_reversal (k : Momentum) (j : Direction) (r : Cell20) :
    star (boundaryPhase k j r) = boundaryPhase (-k) j r := by
  unfold boundaryPhase
  split_ifs
  · change (starRingEnd ℂ) (Complex.exp (Complex.I * (k j : ℂ))) = _
    rw [← Complex.exp_conj]
    simp
  · simp

theorem difference_time_reversal (k : Momentum) (j : Direction) (r s : Cell20) :
    star (difference k j r s) = difference (-k) j r s := by
  unfold difference
  split_ifs <;> simp [boundaryPhase_time_reversal]

theorem curl_time_reversal (k : Momentum) (i : Face20) (j : Electric20) :
    star (curl k i j) = curl (-k) i j := by
  unfold curl
  split_ifs <;> simp only [star_neg, star_zero, difference_time_reversal]

end
end Maxwell.Spectral.PeriodicYee
