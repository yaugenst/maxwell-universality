import Mathlib.Data.Rat.Cast.Lemmas
import Maxwell.Certificate.Interval
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace Maxwell.Certificate

/-- Rational closed boxes. Empty boxes are permitted, so splitting is total. -/
structure Box where
  lo : Fin 3 → ℚ
  hi : Fin 3 → ℚ
  deriving DecidableEq

namespace Box

def Contains (b : Box) (x : Fin 3 → ℝ) : Prop :=
  ∀ i, (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)

def lower (b : Box) (axis : Fin 3) (cut : ℚ) : Box :=
  ⟨b.lo, Function.update b.hi axis cut⟩
def upper (b : Box) (axis : Fin 3) (cut : ℚ) : Box :=
  ⟨Function.update b.lo axis cut, b.hi⟩

theorem split_covers {b : Box} (axis : Fin 3) (cut : ℚ) {x : Fin 3 → ℝ}
    (hx : b.Contains x) : (b.lower axis cut).Contains x ∨ (b.upper axis cut).Contains x := by
  by_cases hc : x axis ≤ (cut : ℝ)
  · left
    intro i
    by_cases hi : i = axis
    · subst i
      simpa [lower] using And.intro (hx axis).1 hc
    · simpa [lower, Function.update_of_ne hi] using hx i
  · right
    intro i
    by_cases hi : i = axis
    · subst i
      simpa [upper] using And.intro (le_of_lt (lt_of_not_ge hc)) (hx axis).2
    · simpa [upper, Function.update_of_ne hi] using hx i

/-- The canonical ordered wedge. The root box supplies coordinate bounds. -/
def Wedge (x : Fin 3 → ℝ) : Prop :=
  x 2 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 + x 1 + x 2 ≤ 3/2

def greedyLo (b : Box) : Fin 3 → ℚ :=
  ![max (b.lo 0) (max (b.lo 1) (b.lo 2)), max (b.lo 1) (b.lo 2), b.lo 2]

def emptyWedgeCheck (b : Box) : Bool :=
  decide (b.hi 0 < b.greedyLo 0 ∨ b.hi 1 < b.greedyLo 1 ∨ b.hi 2 < b.lo 2 ∨
    3/2 < b.greedyLo 0 + b.greedyLo 1 + b.lo 2)

theorem greedyLo_lower {b : Box} {x : Fin 3 → ℝ} (hx : b.Contains x)
    (hw : Wedge x) : ∀ i, (b.greedyLo i : ℝ) ≤ x i := by
  intro i
  fin_cases i
  · change ((max (b.lo 0) (max (b.lo 1) (b.lo 2)) : ℚ) : ℝ) ≤ x 0
    simp only [Rat.cast_max]
    exact max_le (hx 0).1 (max_le ((hx 1).1.trans hw.2.1) ((hx 2).1.trans (hw.1.trans hw.2.1)))
  · change ((max (b.lo 1) (b.lo 2) : ℚ) : ℝ) ≤ x 1
    simp only [Rat.cast_max]
    exact max_le (hx 1).1 ((hx 2).1.trans hw.1)
  · simpa [greedyLo] using (hx 2).1

theorem emptyWedgeCheck_sound {b : Box} (h : b.emptyWedgeCheck = true)
    {x : Fin 3 → ℝ} (hx : b.Contains x) : ¬ Wedge x := by
  intro hw
  have hl := greedyLo_lower hx hw
  have he : b.hi 0 < b.greedyLo 0 ∨ b.hi 1 < b.greedyLo 1 ∨ b.hi 2 < b.lo 2 ∨
      3/2 < b.greedyLo 0 + b.greedyLo 1 + b.lo 2 := of_decide_eq_true h
  rcases he with h0 | h1 | h2 | hs
  · exact (not_lt_of_ge ((hl 0).trans (hx 0).2)) (Rat.cast_lt.mpr h0)
  · exact (not_lt_of_ge ((hl 1).trans (hx 1).2)) (Rat.cast_lt.mpr h1)
  · exact (not_lt_of_ge ((hx 2).1.trans (hx 2).2)) (Rat.cast_lt.mpr h2)
  · have hs' : (3/2 : ℝ) < (b.greedyLo 0 : ℝ) + b.greedyLo 1 + b.lo 2 := by
      have hc : ((3/2 : ℚ) : ℝ) < ((b.greedyLo 0 + b.greedyLo 1 + b.lo 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hs
      norm_num at hc ⊢
      exact hc
    have hh0 := hl 0
    have hh1 := hl 1
    have hh2 := (hx 2).1
    linarith [hw.2.2]

def localRadiusSquared (b : Box) : ℚ :=
  max ((b.lo 0 - 1/2)^2) ((b.hi 0 - 1/2)^2) +
  max ((b.lo 1 - 1/2)^2) ((b.hi 1 - 1/2)^2) +
  max ((b.lo 2 - 1/2)^2) ((b.hi 2 - 1/2)^2)

def localBallCheck (b : Box) : Bool := decide (b.localRadiusSquared ≤ 1/400)

def LocalBall (x : Fin 3 → ℝ) : Prop :=
  (x 0 - 1/2)^2 + (x 1 - 1/2)^2 + (x 2 - 1/2)^2 ≤ 1/400

private theorem square_bound {a x b m : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (ham : a^2 ≤ m) (hbm : b^2 ≤ m) : x^2 ≤ m := by
  by_cases hx : 0 ≤ x
  · have hp : 0 ≤ (b-x)*(b+x) := mul_nonneg (sub_nonneg.mpr hb) (by linarith)
    nlinarith
  · have hp : 0 ≤ (x-a)*(-(a+x)) := mul_nonneg (sub_nonneg.mpr ha) (by linarith)
    nlinarith

theorem localRadiusSquared_bound {b : Box} {x : Fin 3 → ℝ} (hx : b.Contains x) :
    (x 0 - 1/2)^2 + (x 1 - 1/2)^2 + (x 2 - 1/2)^2 ≤ (b.localRadiusSquared : ℝ) := by
  have hc (i : Fin 3) : (x i - 1/2)^2 ≤
      ((max ((b.lo i - 1/2)^2) ((b.hi i - 1/2)^2) : ℚ) : ℝ) := by
    norm_num only [Rat.cast_max, Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact square_bound (sub_le_sub_right (hx i).1 _) (sub_le_sub_right (hx i).2 _)
      (le_max_left _ _) (le_max_right _ _)
  have hh := add_le_add (add_le_add (hc 0) (hc 1)) (hc 2)
  simpa only [localRadiusSquared, Rat.cast_add] using hh

theorem localBallCheck_sound {b : Box} (h : b.localBallCheck = true)
    {x : Fin 3 → ℝ} (hx : b.Contains x) : LocalBall x := by
  have hq : b.localRadiusSquared ≤ 1/400 := of_decide_eq_true h
  have hr : (b.localRadiusSquared : ℝ) ≤ 1/400 := by
    have hh : (b.localRadiusSquared : ℝ) ≤ ((1/400 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    norm_num at hh ⊢
    exact hh
  exact (localRadiusSquared_bound hx).trans hr

end Box

/-- A proposal for a finite closed-box partition. Every node carries an
exact rational cut, and the children inherit their boxes deterministically. -/
inductive CoverTree where
  | leaf (tag : Nat)
  | split (axis : Fin 3) (cut : ℚ) (left right : CoverTree)

namespace CoverTree

def check (leafCheck : Nat → Box → Bool) (b : Box) : CoverTree → Bool
  | .leaf tag => leafCheck tag b
  | .split axis cut left right =>
      check leafCheck (b.lower axis cut) left && check leafCheck (b.upper axis cut) right

/-- This theorem covers every real point, including shared closed faces.
It is independent of the proposal generator and of sampled test points. -/
theorem check_sound (leafCheck : Nat → Box → Bool) (P : (Fin 3 → ℝ) → Prop)
    (leaf_sound : ∀ tag b, leafCheck tag b = true → ∀ x, b.Contains x → P x)
    (tree : CoverTree) (b : Box) (h : tree.check leafCheck b = true)
    (x : Fin 3 → ℝ) (hx : b.Contains x) : P x := by
  induction tree generalizing b with
  | leaf tag => exact leaf_sound tag b h x hx
  | split axis cut left right ihl ihr =>
    have hc : left.check leafCheck (b.lower axis cut) = true ∧
        right.check leafCheck (b.upper axis cut) = true := by simpa [check, Bool.and_eq_true_iff] using h
    rcases b.split_covers axis cut hx with hl | hr
    · exact ihl _ hc.1 hl
    · exact ihr _ hc.2 hr

end CoverTree
end Maxwell.Certificate
