import Maxwell.Certificate.Trigonometric
import Maxwell.Certificate.SchurStep

/-! Verified interval operations for recursive Hermitian Schur certificates.
All witness entries are rational; acceptance checks the enclosed updates and
strictly positive real pivots. -/

namespace Maxwell.Certificate.IntervalMatrix

open Matrix
open Trigonometric
open scoped ComplexOrder

def zeroBall : Ball := ⟨0, 0, le_rfl⟩

theorem zeroBall_contains : zeroBall.Contains 0 := by simp [Ball.Contains, zeroBall]

def realRectangle (a : Ball) : ComplexRectangle := ⟨a, zeroBall⟩

theorem realRectangle_contains {a : Ball} {x : ℝ} (h : a.Contains x) :
    (realRectangle a).Contains (x : ℂ) := ⟨h, zeroBall_contains⟩

def negRectangle (a : ComplexRectangle) : ComplexRectangle := ⟨a.re.neg, a.im.neg⟩

theorem negRectangle_contains {a : ComplexRectangle} {z : ℂ} (h : a.Contains z) :
    (negRectangle a).Contains (-z) := ⟨Ball.contains_neg h.1, Ball.contains_neg h.2⟩

def subRectangle (a b : ComplexRectangle) : ComplexRectangle := a.add (negRectangle b)

theorem subRectangle_contains {a b : ComplexRectangle} {z w : ℂ}
    (ha : a.Contains z) (hb : b.Contains w) : (subRectangle a b).Contains (z - w) := by
  change (a.add (negRectangle b)).Contains (z + -w)
  exact ComplexRectangle.contains_add ha (negRectangle_contains hb)

def reciprocalBall (a : Ball) (h : 0 < a.center - a.radius) : Ball :=
  intervalToBall (Interval.reciprocal (ballToInterval a) h)

theorem reciprocalBall_contains {a : Ball} (h : 0 < a.center - a.radius)
    {x : ℝ} (hx : a.Contains x) : (reciprocalBall a h).Contains (1 / x) :=
  intervalToBall_contains (Interval.reciprocal_contains h (ballToInterval_contains hx))

def divideReal (a : ComplexRectangle) (b : Ball) (h : 0 < b.center - b.radius) :
    ComplexRectangle := a.mul (realRectangle (reciprocalBall b h))

theorem divideReal_contains {a : ComplexRectangle} {b : Ball}
    (h : 0 < b.center - b.radius) {z : ℂ} {x : ℝ}
    (ha : a.Contains z) (hb : b.Contains x) : (divideReal a b h).Contains (z / (x : ℂ)) := by
  have hh := ComplexRectangle.contains_mul ha
    (realRectangle_contains (reciprocalBall_contains h hb))
  simpa only [divideReal, Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, div_eq_mul_inv, one_mul] using hh

abbrev Enclosure (n : ℕ) := Matrix (Fin n) (Fin n) ComplexRectangle

def Contains {n : ℕ} (a : Enclosure n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, (a i j).Contains (A i j)

/-- The source elimination kernel stores and updates only the lower triangle. -/
def LowerContains {n : ℕ} (a : Enclosure n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, j ≤ i → (a i j).Contains (A i j)

def hermitianCompletion {n : ℕ} (a : Enclosure n) : Enclosure n :=
  fun i j => if j ≤ i then a i j else (a j i).conjugate

theorem hermitianCompletion_contains {n : ℕ} {a : Enclosure n}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (ha : LowerContains a A) :
    Contains (hermitianCompletion a) A := by
  intro i j
  dsimp [hermitianCompletion]
  split_ifs with hij
  · exact ha i j hij
  · rw [← hA.apply i j]
    exact ComplexRectangle.contains_conjugate (ha j i (le_of_lt (lt_of_not_ge hij)))

def pivotLower {n : ℕ} (a : Enclosure (n + 1)) : ℚ :=
  (a 0 0).re.center - (a 0 0).re.radius

theorem positive_pivot {n : ℕ} {a : Enclosure (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : 0 < pivotLower a) (hA : Contains a A) : 0 < (A 0 0).re := by
  have hlo := (ballToInterval_contains (hA 0 0).1).1
  exact (Rat.cast_pos.mpr h).trans_le hlo

def step {n : ℕ} (a : Enclosure (n + 1)) (h : 0 < pivotLower a) : Enclosure n :=
  fun i j => subRectangle (a i.succ j.succ)
    (divideReal ((a i.succ 0).mul ((a j.succ 0).conjugate)) (a 0 0).re h)

theorem step_contains {n : ℕ} {a : Enclosure (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : 0 < pivotLower a) (hA : Contains a A) :
    Contains (step a h) (fun i j =>
      A i.succ j.succ - A i.succ 0 * star (A j.succ 0) / ((A 0 0).re : ℂ)) := by
  intro i j
  exact subRectangle_contains (hA i.succ j.succ)
    (divideReal_contains h (ComplexRectangle.contains_mul (hA i.succ 0)
      (ComplexRectangle.contains_conjugate (hA j.succ 0))) (hA 0 0).1)

def subsetCheck {n : ℕ} (a b : Enclosure n) : Bool :=
  decide (∀ i j, rectangleSubsetCheck (a i j) (b i j) = true)

theorem subsetCheck_sound {n : ℕ} {a b : Enclosure n}
    (h : subsetCheck a b = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Contains a A) : Contains b A := by
  have hh : ∀ i j, rectangleSubsetCheck (a i j) (b i j) = true := of_decide_eq_true h
  exact fun i j => rectangleSubsetCheck_sound (hh i j) (hA i j)

/-- Each elimination step proposes the next enclosure, permitting bounded-size
dyadic data instead of retaining growing exact rational expressions. -/
inductive Proposal : ℕ → Type
  | empty : Proposal 0
  | next {n : ℕ} (enclosure : Enclosure n) (tail : Proposal n) : Proposal (n + 1)

def accepts : {n : ℕ} → Enclosure n → Proposal n → Bool
  | 0, _, .empty => true
  | _ + 1, a, .next b tail =>
      if h : 0 < pivotLower a then subsetCheck (step a h) b && accepts b tail else false

theorem accepts_sound {n : ℕ} {a : Enclosure n} (w : Proposal n)
    (h : accepts a w = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ha : Contains a A) : A.PosSemidef := by
  induction w with
  | empty =>
      have hz : A = 0 := by ext i; exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | @next n b tail ih =>
      simp only [accepts] at h
      split_ifs at h with hp
      · have hh := Bool.and_eq_true_iff.mp h
        apply SchurStep.posSemidef_of_schur hA (positive_pivot hp ha)
        exact ih hh.2 (SchurStep.schur_isHermitian hA)
          (subsetCheck_sound hh.1 (step_contains hp ha))

theorem accepts_lower_sound {n : ℕ} {a : Enclosure n} (w : Proposal n)
    (h : accepts (hermitianCompletion a) w = true)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (ha : LowerContains a A) :
    A.PosSemidef := accepts_sound w h hA (hermitianCompletion_contains hA ha)

end Maxwell.Certificate.IntervalMatrix
