import Maxwell.Defect.DyadicSqrt
import Mathlib.Analysis.Normed.Module.Normalize

/-! Rational normalization by an upper square-root enclosure. The computed
vector never has norm above one, and its error has an explicit dyadic bound. -/

namespace Maxwell.Defect.RationalNormalize

open NormedSpace

variable {n : ℕ}

def denominator (v : Fin n → ℚ) (B : ℚ) (p : ℕ) : ℚ :=
  B * DyadicSqrt.upper (rationalNormSq v / B ^ 2) p

def vector (v : Fin n → ℚ) (B : ℚ) (p : ℕ) : Fin n → ℚ :=
  (denominator v B p)⁻¹ • v

theorem vector_cast (v : Fin n → ℚ) (B : ℚ) (p : ℕ) :
    rationalVector (vector v B p) = (denominator v B p : ℝ)⁻¹ • rationalVector v := by
  ext i
  simp [vector, rationalVector]

/-- The computed rational divisor is above the actual norm and differs
by at most B times the dyadic bisection width. -/
theorem denominator_spec (v : Fin n → ℚ) (B b : ℚ) (p : ℕ)
    (hB : 0 < B) (hb : 0 < b)
    (hlower : (b : ℝ) ≤ ‖rationalVector v‖) (hupper : ‖rationalVector v‖ ≤ (B : ℝ)) :
    0 < denominator v B p ∧
      ‖rationalVector v‖ ≤ (denominator v B p : ℝ) ∧
      (denominator v B p : ℝ) - ‖rationalVector v‖ ≤ (B : ℝ) * ((2 : ℝ) ^ p)⁻¹ ∧
      denominator v B p ≤ B := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hnorm : 0 < ‖rationalVector v‖ := hb'.trans_le hlower
  have hv0 : 0 ≤ rationalNormSq v := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hvB : rationalNormSq v ≤ B ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (rationalVector v)) hupper 2
    rw [← rationalNormSq_cast] at hh
    exact_mod_cast hh
  have hx0 : 0 ≤ rationalNormSq v / B ^ 2 := div_nonneg hv0 (sq_nonneg B)
  have hx1 : rationalNormSq v / B ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hB)).mpr hvB
  have hroot : Real.sqrt ((rationalNormSq v / B ^ 2 : ℚ) : ℝ) =
      ‖rationalVector v‖ / (B : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_pow, rationalNormSq_cast]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_pos hnorm, abs_of_pos hB']
  obtain ⟨hlo, herr, hhi⟩ := DyadicSqrt.upper_sqrt_spec _ hx0 hx1 p
  rw [hroot] at hlo herr
  have hden : (denominator v B p : ℝ) =
      (B : ℝ) * (DyadicSqrt.upper (rationalNormSq v / B ^ 2) p : ℝ) := by
    simp only [denominator, Rat.cast_mul]
  have hl : ‖rationalVector v‖ ≤ (denominator v B p : ℝ) := by
    rw [hden]
    exact (div_le_iff₀ hB').mp hlo |>.trans_eq (mul_comm _ _)
  refine ⟨by exact_mod_cast hnorm.trans_le hl, hl, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left herr hB'.le
    rw [mul_sub, mul_div_cancel₀ _ hB'.ne'] at hh
    simpa only [hden] using hh
  · exact mul_le_of_le_one_right hB.le hhi

/-- Upper-root normalization is rational, has norm at most one, and
approaches the actual unit direction with an explicit B/b error factor. -/
theorem vector_spec (v : Fin n → ℚ) (B b : ℚ) (p : ℕ)
    (hB : 0 < B) (hb : 0 < b)
    (hlower : (b : ℝ) ≤ ‖rationalVector v‖) (hupper : ‖rationalVector v‖ ≤ (B : ℝ)) :
    ‖rationalVector (vector v B p)‖ ≤ 1 ∧
      ‖rationalVector (vector v B p) - NormedSpace.normalize (rationalVector v)‖ ≤
        ((B / b : ℚ) : ℝ) * ((2 : ℝ) ^ p)⁻¹ := by
  obtain ⟨hden0, hden, herr, _⟩ := denominator_spec v B b p hB hb hlower hupper
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : (0 : ℝ) < denominator v B p := by exact_mod_cast hden0
  have hnorm : 0 < ‖rationalVector v‖ := hb'.trans_le hlower
  have hunit : ‖NormedSpace.normalize (rationalVector v)‖ = 1 :=
    norm_normalize (norm_pos_iff.mp hnorm)
  have hrep : rationalVector (vector v B p) =
      (‖rationalVector v‖ / (denominator v B p : ℝ)) • NormedSpace.normalize (rationalVector v) := by
    rw [vector_cast, div_eq_mul_inv, mul_comm, ← smul_smul, norm_smul_normalize]
  have hratio : ‖rationalVector v‖ / (denominator v B p : ℝ) ≤ 1 := (div_le_one hs).mpr hden
  have hratio0 : 0 ≤ ‖rationalVector v‖ / (denominator v B p : ℝ) := div_nonneg hnorm.le hs.le
  constructor
  · rw [hrep, norm_smul, hunit, mul_one, Real.norm_eq_abs, abs_of_nonneg hratio0]
    exact hratio
  · have hdiff : rationalVector (vector v B p) - NormedSpace.normalize (rationalVector v) =
        (‖rationalVector v‖ / (denominator v B p : ℝ) - 1) • NormedSpace.normalize (rationalVector v) := by
      rw [sub_smul, one_smul, hrep]
    rw [hdiff, norm_smul, hunit, mul_one, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hratio)]
    calc
      _ = ((denominator v B p : ℝ) - ‖rationalVector v‖) / (denominator v B p : ℝ) := by
        rw [sub_div, div_self hs.ne']
        ring
      _ ≤ ((denominator v B p : ℝ) - ‖rationalVector v‖) / (b : ℝ) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hden) hb' (hlower.trans hden)
      _ ≤ ((B : ℝ) * ((2 : ℝ) ^ p)⁻¹) / (b : ℝ) := div_le_div_of_nonneg_right herr hb'.le
      _ = _ := by push_cast; ring

end Maxwell.Defect.RationalNormalize
