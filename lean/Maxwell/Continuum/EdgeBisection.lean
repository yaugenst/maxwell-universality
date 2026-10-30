import Maxwell.Continuum.CalibrationInterval
import Mathlib.Tactic

/-! A total finite rational bisection with certified overlap. A sign decision
may have an error of one sixty-fourth of the current bracket width. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate

def edgeStep (I : Interval) (negative : Bool) : Interval :=
  if negative then
    ⟨I.lo,I.midpoint+I.width/64,by
      have := I.ordered
      unfold Interval.midpoint Interval.width
      linarith⟩
  else
    ⟨I.midpoint-I.width/64,I.hi,by
      have := I.ordered
      unfold Interval.midpoint Interval.width
      linarith⟩

theorem edgeStep_width (I : Interval) (negative : Bool) :
    (edgeStep I negative).width=(33/64 : ℚ)*I.width := by
  cases negative <;> simp only [edgeStep,Bool.false_eq_true,↓reduceIte,
    Interval.width,Interval.midpoint] <;> ring

theorem edgeStep_inside (I : Interval) (negative : Bool) :
    I.lo≤(edgeStep I negative).lo ∧ (edgeStep I negative).hi≤I.hi := by
  have := I.ordered
  cases negative <;> simp only [edgeStep,Bool.false_eq_true,↓reduceIte,
    Interval.width,Interval.midpoint] <;> constructor <;> linarith

theorem edgeStep_contains (I : Interval) (negative : Bool) {r : ℝ} (hr : I.Contains r)
    (hneg : negative=true → r≤(I.midpoint : ℝ)+(I.width : ℝ)/64)
    (hpos : negative=false → (I.midpoint : ℝ)-(I.width : ℝ)/64≤r) :
    (edgeStep I negative).Contains r := by
  cases negative
  · exact ⟨by simpa only [edgeStep,Bool.false_eq_true,↓reduceIte,Rat.cast_sub,
      Rat.cast_div,Rat.cast_ofNat] using hpos rfl,hr.2⟩
  · exact ⟨hr.1,by simpa only [edgeStep,↓reduceIte,Rat.cast_add,
      Rat.cast_div,Rat.cast_ofNat] using hneg rfl⟩

def edgeBrackets (decideNegative : ℚ → ℕ → Bool) (base : ℕ) (I : Interval) : ℕ → Interval
  | 0 => I
  | k+1 => let J := edgeBrackets decideNegative base I k
      edgeStep J (decideNegative J.midpoint (base+k+6))

theorem edgeBrackets_width (decideNegative : ℚ → ℕ → Bool) (base : ℕ) (I : Interval) (k : ℕ) :
    (edgeBrackets decideNegative base I k).width=(33/64 : ℚ)^k*I.width := by
  induction k with
  | zero => simp [edgeBrackets]
  | succ k ih => rw [edgeBrackets,edgeStep_width,ih,pow_succ]; ring

theorem edgeBrackets_inside (decideNegative : ℚ → ℕ → Bool) (base : ℕ) (I : Interval) (k : ℕ) :
    I.lo≤(edgeBrackets decideNegative base I k).lo ∧
      (edgeBrackets decideNegative base I k).hi≤I.hi := by
  induction k with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ k ih =>
    have h := edgeStep_inside (edgeBrackets decideNegative base I k)
      (decideNegative (edgeBrackets decideNegative base I k).midpoint (base+k+6))
    exact ⟨ih.1.trans h.1,h.2.trans ih.2⟩

theorem edgeBrackets_positive_width (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (hI : 0<I.width) (k : ℕ) :
    0<(edgeBrackets decideNegative base I k).width := by
  rw [edgeBrackets_width]
  positivity

theorem edgeBrackets_precision (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (hI : (1/2 : ℚ)^base≤I.width) (k : ℕ) :
    (1/2 : ℚ)^(base+k+6)≤(edgeBrackets decideNegative base I k).width/64 := by
  rw [edgeBrackets_width,show base+k+6=base+k+6 by rfl,pow_add,pow_add]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ)≤1/2) (by norm_num : (1/2 : ℚ)≤33/64) k
  have hprod := mul_le_mul hp hI (by positivity) (by positivity)
  norm_num only [show (1/2 : ℚ)^6=1/64 by norm_num]
  nlinarith only [hprod]

/-- A one-sided approximate sign comparison is sufficient, including equality. -/
theorem edgeBrackets_contains (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (hI : (1/2 : ℚ)^base≤I.width) {r : ℝ} (hr : I.Contains r)
    (hdecision : ∀ (q : ℚ) (P : ℕ), I.lo≤q → q≤I.hi →
      (decideNegative q P=true → r≤(q : ℝ)+(1/2 : ℝ)^P) ∧
      (decideNegative q P=false → (q : ℝ)-(1/2 : ℝ)^P≤r)) (k : ℕ) :
    (edgeBrackets decideNegative base I k).Contains r := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    let J := edgeBrackets decideNegative base I k
    have hins := edgeBrackets_inside decideNegative base I k
    have hlo : I.lo≤J.midpoint := by
      have horder := J.ordered
      change I.lo≤(J.lo+J.hi)/2
      linarith [hins.1]
    have hhi : J.midpoint≤I.hi := by
      have horder := J.ordered
      change (J.lo+J.hi)/2≤I.hi
      linarith [hins.2]
    have hp : (1/2 : ℝ)^(base+k+6)≤(J.width : ℝ)/64 := by
      simpa only [J,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (edgeBrackets_precision decideNegative base I hI k)
    have hd := hdecision J.midpoint (base+k+6) hlo hhi
    exact edgeStep_contains J _ ih (fun h => (hd.1 h).trans (by linarith))
      (fun h => (by linarith : (J.midpoint : ℝ)-(J.width : ℝ)/64≤
        (J.midpoint : ℝ)-(1/2 : ℝ)^(base+k+6)).trans (hd.2 h))

theorem edgeBrackets_target_width (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (B N : ℕ) (hI : I.width≤(2 : ℚ)^B) :
    (edgeBrackets decideNegative base I (2*(N+B))).width≤(1/2 : ℚ)^N := by
  rw [edgeBrackets_width,pow_mul]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ)≤(33/64)^2)
    (by norm_num : (33/64 : ℚ)^2≤1/2) (N+B)
  calc
    _ ≤ (1/2 : ℚ)^(N+B)*(2 : ℚ)^B := mul_le_mul hp hI I.width_nonneg (by positivity)
    _ = _ := by rw [pow_add,mul_assoc,← mul_pow]; norm_num

#print axioms edgeBrackets_contains
#print axioms edgeBrackets_target_width

end Maxwell.Continuum.Calibration
