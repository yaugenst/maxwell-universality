import Maxwell.Certificate.DyadicRectangle
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The Hermitian part of an actual rectangular compression preserves its
real quadratic form. Integer interval dot checks enclose that Hermitian part,
so signed positive-semidefinite certificates apply to the actual pairing. -/

noncomputable section

namespace Maxwell.Certificate.HermitianCompression

open Matrix
open scoped BigOperators InnerProduct ComplexOrder

variable {m n : ℕ}

/-- The Hermitian compression of the trial columns and their actual images. -/
def matrix (F A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (F.conjTranspose * A + A.conjTranspose * F)

@[simp] theorem matrix_apply (F A : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) :
    matrix F A i j = ((F.conjTranspose * A) i j + (A.conjTranspose * F) i j) / 2 := by
  simp [matrix, div_eq_mul_inv, mul_comm]

theorem isHermitian (F A : Matrix (Fin m) (Fin n) ℂ) : (matrix F A).IsHermitian := by
  unfold Matrix.IsHermitian matrix
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, add_comm]

theorem inner_cross (F A : Matrix (Fin m) (Fin n) ℂ)
    (p : EuclideanSpace ℂ (Fin n)) :
    inner ℂ p ((F.conjTranspose * A).toEuclideanLin p) =
      inner ℂ (F.toEuclideanLin p) (A.toEuclideanLin p) := by
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

/-- Symmetrization changes no real quadratic value, for every complex input. -/
theorem quadratic_re (F A : Matrix (Fin m) (Fin n) ℂ)
    (p : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ p ((matrix F A).toEuclideanLin p)).re =
      (inner ℂ (F.toEuclideanLin p) (A.toEuclideanLin p)).re := by
  simp only [matrix, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    inner_smul_right, inner_add_right, inner_cross]
  have h := inner_re_symm (𝕜 := ℂ) (F.toEuclideanLin p) (A.toEuclideanLin p)
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
  norm_num
  change (inner ℂ (F.toEuclideanLin p) (A.toEuclideanLin p)).re =
    (inner ℂ (A.toEuclideanLin p) (F.toEuclideanLin p)).re at h
  linarith

/-- A shifted PSD certificate gives an actual lower quadratic bound. -/
theorem matrix_lower (H : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    (hH : (H - (a : ℂ) • 1).PosSemidef) (p : EuclideanSpace ℂ (Fin n)) :
    a * ‖p‖ ^ 2 ≤ (inner ℂ p (H.toEuclideanLin p)).re := by
  have h := (Matrix.isPositive_toEuclideanLin_iff.mpr hH).2 p
  rw [inner_re_symm] at h
  change 0 ≤ (inner ℂ p ((H - (a : ℂ) • 1).toEuclideanLin p)).re at h
  simp only [map_sub, map_smul, Matrix.toLpLin_one, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← Complex.ofReal_pow] at h
  linarith

theorem signed_lower (F A : Matrix (Fin m) (Fin n) ℂ) (sign a : ℝ)
    (hH : ((sign : ℂ) • matrix F A - (a : ℂ) • 1).PosSemidef)
    (p : EuclideanSpace ℂ (Fin n)) :
    a * ‖p‖ ^ 2 ≤ sign * (inner ℂ (F.toEuclideanLin p) (A.toEuclideanLin p)).re := by
  have h := matrix_lower ((sign : ℂ) • matrix F A) a hH p
  simpa only [map_smul, LinearMap.smul_apply, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, quadratic_re] using h

end Maxwell.Certificate.HermitianCompression

namespace Maxwell.Certificate.DyadicRectangle

/-- A rectangle is convex: averaging two enclosed values needs no widening. -/
theorem average_contains {p : ℕ} {a : DyadicRectangle} {z w : ℂ}
    (hz : a.Contains p z) (hw : a.Contains p w) : a.Contains p ((z + w) / 2) := by
  have average_bound (x y c r : ℝ) (hx : |x - c| ≤ r) (hy : |y - c| ≤ r) :
      |(x + y) / 2 - c| ≤ r := by
    rw [abs_le] at hx hy ⊢
    constructor <;> linarith
  constructor
  · simp only [Complex.div_ofNat_re, Complex.add_re]
    have h := average_bound (z.re * 2 ^ p) (w.re * 2 ^ p) a.re a.radius hz.1 hw.1
    convert h using 1
    congr 1
    ring
  · simp only [Complex.div_ofNat_im, Complex.add_im]
    have h := average_bound (z.im * 2 ^ p) (w.im * 2 ^ p) a.im a.radius hz.2 hw.2
    convert h using 1
    congr 1
    ring

@[simp] theorem conjugate_conjugate (a : DyadicRectangle) :
    a.conjugate.conjugate = a := by
  cases a
  simp [conjugate]

end Maxwell.Certificate.DyadicRectangle

namespace Maxwell.Certificate.HermitianCompression

open Matrix
open scoped BigOperators

variable {m n : ℕ}

/-- The two checked oriented pairings enclose the Hermitian average at this
entry, even when the raw rectangular compression is not Hermitian. -/
theorem entry_contains {precision : ℕ}
    (F A : Matrix (Fin m) (Fin n) ℂ)
    (f a : Matrix (Fin m) (Fin n) DyadicRectangle) (c : DyadicRectangle)
    (i j : Fin n)
    (hf : ∀ k l, (f k l).Contains precision (F k l))
    (ha : ∀ k l, (a k l).Contains precision (A k l))
    (hforward : DyadicRectangle.dotCheck precision precision
      (fun k => (f k i).conjugate) (fun k => a k j) c = true)
    (hreverse : DyadicRectangle.dotCheck precision precision
      (fun k => (f k j).conjugate) (fun k => a k i) c.conjugate = true) :
    c.Contains precision (matrix F A i j) := by
  have hfirst : c.Contains precision ((F.conjTranspose * A) i j) :=
    DyadicRectangle.dotCheck_sound hforward
      (fun k => DyadicRectangle.conjugate_contains (hf k i)) (fun k => ha k j)
  have hsecond : c.conjugate.Contains precision ((F.conjTranspose * A) j i) :=
    DyadicRectangle.dotCheck_sound hreverse
      (fun k => DyadicRectangle.conjugate_contains (hf k j)) (fun k => ha k i)
  have hstar : star ((F.conjTranspose * A) j i) = (A.conjTranspose * F) i j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j)
      (Matrix.conjTranspose_mul F.conjTranspose A)
    simpa only [Matrix.conjTranspose_apply, Matrix.conjTranspose_conjTranspose] using h
  have hsecond' : c.Contains precision ((A.conjTranspose * F) i j) := by
    simpa only [DyadicRectangle.conjugate_conjugate, hstar] using
      DyadicRectangle.conjugate_contains hsecond
  rw [matrix_apply]
  exact DyadicRectangle.average_contains hfirst hsecond'

/-- Bind a complete integer dot-check matrix to the actual Hermitian
compression, without replacing the supplied complex trial fields. -/
theorem contains {precision : ℕ}
    (F A : Matrix (Fin m) (Fin n) ℂ)
    (f a : Matrix (Fin m) (Fin n) DyadicRectangle)
    (c : Matrix (Fin n) (Fin n) DyadicRectangle)
    (hf : ∀ k l, (f k l).Contains precision (F k l))
    (ha : ∀ k l, (a k l).Contains precision (A k l))
    (hchecks : ∀ i j, (DyadicRectangle.dotCheck precision precision
      (fun k => (f k i).conjugate) (fun k => a k j) (c i j) &&
        DyadicRectangle.dotCheck precision precision
          (fun k => (f k j).conjugate) (fun k => a k i) (c i j).conjugate) = true) :
    ∀ i j, (c i j).Contains precision (matrix F A i j) := by
  intro i j
  have h := Bool.and_eq_true_iff.mp (hchecks i j)
  exact entry_contains F A f a (c i j) i j hf ha h.1 h.2

end Maxwell.Certificate.HermitianCompression
