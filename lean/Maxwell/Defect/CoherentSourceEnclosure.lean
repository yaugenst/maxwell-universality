import Maxwell.Defect.CoherentCubeProfile
import Maxwell.Defect.WeightSearch
import Maxwell.Defect.EdgeSourceEnclosure

/-! Executable rational enclosures of the same physical coherent source. -/
namespace Maxwell.Defect.ScalarDefect

open Spectral Spectral.Lattice Spectral.Bloch

def trimPhase (k n : Site) : ℚ := (-1) ^ (∑ j, k j * n j)

theorem trimPhase_abs (k n : Site) : |(trimPhase k n : ℝ)| = 1 := by
  simp [trimPhase, abs_zpow]

theorem mFourier_trim_eq (k n : Site) :
    UnitAddTorus.mFourier n (momentumTorus (fun j => Real.pi * (k j : ℝ))) =
      (trimPhase k n : ℂ) := by
  rw [mFourier_momentum n (WithLp.toLp 2 (fun j => Real.pi * (k j : ℝ)))]
  have he : Complex.I *
      (inner ℝ (WithLp.toLp 2 (fun j => Real.pi * (k j : ℝ))) (periodVector n) : ℂ) =
      ((∑ j, k j * n j : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    simp only [PiLp.inner_apply, periodVector, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three]
    push_cast
    ring
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  simp [trimPhase]

def rationalCoherentSource (L : ℕ) (k : Site) (φ : Edge20 → ℚ)
    (weights : Fin (edges (cube L)).card → ℚ) : Fin (edges (cube L)).card → ℚ :=
  fun i => weights i * trimPhase k (edgeCellEquiv (edgeEmbedding (cube L) i)).2 *
    φ (edgeCellEquiv (edgeEmbedding (cube L) i)).1

theorem coherent_real_coordinate (L : ℕ) (k : Site) (φ : EuclideanSpace ℂ Edge20)
    (i : Fin (edges (cube L)).card) :
    realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
      (momentumTorus (fun j => Real.pi * (k j : ℝ))))) i =
      Real.sqrt (coordinateWeight (cube L) i : ℝ) *
        (trimPhase k (edgeCellEquiv (edgeEmbedding (cube L) i)).2 : ℝ) *
          (φ (edgeCellEquiv (edgeEmbedding (cube L) i)).1).re := by
  simp [coherentCoordinates, mFourier_trim_eq, Complex.mul_re]

/-- Coordinate errors in the finite edge eigenvector and square-root
weights give an explicit rational error for the complete cube source. -/
theorem rationalCoherentSource_error (L : ℕ) (k : Site) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ‖φ‖ = 1) (q : Edge20 → ℚ)
    (weights : Fin (edges (cube L)).card → ℚ) {ε δ : ℚ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hq : ∀ r, |(φ r).re - (q r : ℝ)| ≤ (ε : ℝ))
    (hw : ∀ i, 0 ≤ weights i ∧ weights i ≤ 1 ∧
      |weights i ^ 2 - coordinateWeight (cube L) i| ≤ δ ^ 2) :
    ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
        (momentumTorus (fun j => Real.pi * (k j : ℝ))))) -
      rationalVector (rationalCoherentSource L k q weights)‖ ≤
        (((edges (cube L)).card + 1 : ℕ) : ℝ) * ((ε : ℝ) + δ) := by
  let x := realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
        (momentumTorus (fun j => Real.pi * (k j : ℝ))))) -
      rationalVector (rationalCoherentSource L k q weights)
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hδr : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hcoord (i : Fin (edges (cube L)).card) : |x i| ≤ (ε : ℝ) + δ := by
    have hwi := hw i
    have hW : 0 ≤ coordinateWeight (cube L) i :=
      le_trans (by norm_num) (coordinateWeight_bounds (cube L) i).1
    have herr := rational_sqrt_error (coordinateWeight (cube L) i) (weights i) δ hW hwi.1 hδ hwi.2.2
    have hφi : |(φ (edgeCellEquiv (edgeEmbedding (cube L) i)).1).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans ((PiLp.norm_apply_le _ _).trans_eq hφ)
    have hwr : |(weights i : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by exact_mod_cast hwi.1)]
      exact_mod_cast hwi.2.1
    change |realCoordinatePart _ i - (rationalCoherentSource L k q weights i : ℝ)| ≤ _
    rw [coherent_real_coordinate]
    simp only [rationalCoherentSource, Rat.cast_mul]
    let p := (trimPhase k (edgeCellEquiv (edgeEmbedding (cube L) i)).2 : ℝ)
    let f := (φ (edgeCellEquiv (edgeEmbedding (cube L) i)).1).re
    let a := Real.sqrt (coordinateWeight (cube L) i : ℝ)
    let b := (weights i : ℝ)
    let v := (q (edgeCellEquiv (edgeEmbedding (cube L) i)).1 : ℝ)
    change |a * p * f - b * p * v| ≤ _
    have hid : a * p * f - b * p * v = p * ((a - b) * f + b * (f - v)) := by ring
    rw [hid, abs_mul, trimPhase_abs, one_mul]
    calc
      |(a - b) * f + b * (f - v)| ≤ |a - b| * |f| + |b| * |f - v| := by
        simpa only [abs_mul] using abs_add_le ((a - b) * f) (b * (f - v))
      _ ≤ (δ : ℝ) * 1 + 1 * ε := add_le_add
        (mul_le_mul (by simpa only [a, b, abs_sub_comm] using herr) hφi (abs_nonneg _) hδr)
        (mul_le_mul hwr (hq _) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hs : ‖x‖ ^ 2 ≤ ((edges (cube L)).card : ℝ) * ((ε : ℝ) + δ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i, (x i) ^ 2) ≤ ∑ _i : Fin (edges (cube L)).card, ((ε : ℝ) + δ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := pow_le_pow_left₀ (abs_nonneg (x i)) (hcoord i) 2
        simpa only [sq_abs] using h
      _ = _ := by simp
  have hN : (0 : ℝ) ≤ (edges (cube L)).card := Nat.cast_nonneg _
  have hbig : ((edges (cube L)).card : ℝ) ≤ (((edges (cube L)).card : ℝ) + 1) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hbig (sq_nonneg ((ε : ℝ) + δ))
  change ‖x‖ ≤ _
  push_cast
  apply (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp
  calc
    ‖x‖ ^ 2 ≤ ((edges (cube L)).card : ℝ) * ((ε : ℝ) + δ) ^ 2 := hs
    _ ≤ (((edges (cube L)).card : ℝ) + 1) ^ 2 * ((ε : ℝ) + δ) ^ 2 := hh
    _ = _ := by ring

def coherentSourceSequence (L : ℕ) (k : Site) (q : ℕ → Edge20 → ℚ)
    (stage : ℕ) : Fin (edges (cube L)).card → ℚ :=
  rationalCoherentSource L k (q stage)
    (sqrtWeightSearch (coordinateWeight (cube L)) (EdgeSourceEnclosure.accuracy stage)
      (fun i => le_trans (by norm_num) (coordinateWeight_bounds (cube L) i).1)
      (fun i => (coordinateWeight_bounds (cube L) i).2)
      (EdgeSourceEnclosure.accuracy_pos stage))

def coherentSourceError (L stage : ℕ) : ℚ :=
  2 * ((edges (cube L)).card + 1) * EdgeSourceEnclosure.accuracy stage

theorem coherentSourceError_pos (L stage : ℕ) : 0 < coherentSourceError L stage := by
  unfold coherentSourceError
  have h := EdgeSourceEnclosure.accuracy_pos stage
  positivity

theorem coherentSourceError_tendsto (L : ℕ) :
    Filter.Tendsto (fun stage => (coherentSourceError L stage : ℝ))
      Filter.atTop (nhds 0) := by
  have h := EdgeSourceEnclosure.accuracy_tendsto.const_mul
    (2 * ((edges (cube L)).card + 1 : ℝ))
  simpa only [coherentSourceError, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one, mul_zero] using h

theorem coherentSourceSequence_error (L : ℕ) (k : Site) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ‖φ‖ = 1) (q : ℕ → Edge20 → ℚ)
    (hq : ∀ stage r, |(φ r).re - (q stage r : ℝ)| ≤ (EdgeSourceEnclosure.accuracy stage : ℝ))
    (stage : ℕ) :
    ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
        (momentumTorus (fun j => Real.pi * (k j : ℝ))))) -
      rationalVector (coherentSourceSequence L k q stage)‖ ≤ (coherentSourceError L stage : ℝ) := by
  have h := rationalCoherentSource_error L k φ hφ (q stage) _
    (EdgeSourceEnclosure.accuracy_pos stage).le (EdgeSourceEnclosure.accuracy_pos stage).le
    (hq stage) (sqrtWeightSearch_spec (coordinateWeight (cube L))
      (EdgeSourceEnclosure.accuracy stage)
      (fun i => le_trans (by norm_num) (coordinateWeight_bounds (cube L) i).1)
      (fun i => (coordinateWeight_bounds (cube L) i).2)
      (EdgeSourceEnclosure.accuracy_pos stage))
  convert h using 1
  all_goals simp only [coherentSourceSequence, coherentSourceError, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  all_goals ring

def coherentSourceBound (L : ℕ) (k : Site) (q : ℕ → Edge20 → ℚ) : ℚ :=
  EdgeSourceEnclosure.referenceBound (coherentSourceSequence L k q 0) + coherentSourceError L 0

theorem coherentSourceBound_pos (L : ℕ) (k : Site) (q : ℕ → Edge20 → ℚ) :
    0 < coherentSourceBound L k q :=
  add_pos (EdgeSourceEnclosure.referenceBound_pos _) (coherentSourceError_pos L 0)

theorem coherentSource_norm_le_bound (L : ℕ) (k : Site) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ‖φ‖ = 1) (q : ℕ → Edge20 → ℚ)
    (hq : ∀ stage r, |(φ r).re - (q stage r : ℝ)| ≤ (EdgeSourceEnclosure.accuracy stage : ℝ)) :
    ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
      (momentumTorus (fun j => Real.pi * (k j : ℝ)))))‖ ≤ (coherentSourceBound L k q : ℝ) := by
  have he := coherentSourceSequence_error L k φ hφ q hq 0
  have hb := EdgeSourceEnclosure.reference_norm_le (coherentSourceSequence L k q 0)
  have ht := norm_le_norm_add_norm_sub
    (rationalVector (coherentSourceSequence L k q 0))
    (realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
      (momentumTorus (fun j => Real.pi * (k j : ℝ))))))
  rw [norm_sub_rev] at ht
  change _ ≤ ((EdgeSourceEnclosure.referenceBound _ + coherentSourceError L 0 : ℚ) : ℝ)
  push_cast
  linarith

end Maxwell.Defect.ScalarDefect
