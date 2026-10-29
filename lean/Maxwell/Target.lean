import Maxwell.Source
import Maxwell.TargetGeometry
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Pi.Bounds

/-! Actual finite Maxwell systems and fixed-width weighted local readout.

Every word is a bounded finite type on every draw. The decoder consumes only
these words and rational calibration coefficients, including on bad draws.
No existence, calibration, complexity, or residual-recovery conclusion is
stored as a field of an encoded instance.
-/

namespace Maxwell.Target

/-- The fixed material interval and frequency satisfy the stated discrete
sampling inequality, independently of the input and random draw. -/
theorem fixed_sampling_inequality : (25 : ℝ) / 64 < 4 * Real.pi ^ 2 / 100 := by
  nlinarith [Real.pi_gt_d2, sq_nonneg (Real.pi - 3.14)]

theorem fixed_sampling_wavenumber : (1 : ℝ) / 8 * Real.sqrt 25 ≤ 2 * Real.pi / 10 := by
  have hs : Real.sqrt (25 : ℝ) = 5 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 25)
    have hp := Real.sqrt_nonneg (25 : ℝ)
    nlinarith
  rw [hs]
  linarith [Real.pi_gt_d2]

structure FixedPointFormat where
  integerBits : ℕ
  fractionalBits : ℕ
  deriving DecidableEq

namespace FixedPointFormat

def width (F : FixedPointFormat) : ℕ := 1 + F.integerBits + F.fractionalBits

/-- Offset-binary word of exactly the prescribed width, including sign. -/
abbrev Word (F : FixedPointFormat) := Fin (2 ^ F.width)

def numerator (F : FixedPointFormat) (w : F.Word) : ℤ :=
  (w.val : ℤ) - 2 ^ (F.integerBits + F.fractionalBits)

def value (F : FixedPointFormat) (w : F.Word) : ℚ :=
  (F.numerator w : ℚ) / (2 : ℚ) ^ F.fractionalBits

/-- A half-open range compatible with every representable signed word. -/
def InRange (F : FixedPointFormat) (x : ℝ) : Prop :=
  -(2 : ℝ) ^ F.integerBits ≤ x ∧ x < (2 : ℝ) ^ F.integerBits

theorem word_card (F : FixedPointFormat) : Fintype.card F.Word = 2 ^ F.width := by
  simp [Word]

theorem numerator_bounds (F : FixedPointFormat) (w : F.Word) :
    -(2 : ℤ) ^ (F.integerBits + F.fractionalBits) ≤ F.numerator w ∧
      F.numerator w < (2 : ℤ) ^ (F.integerBits + F.fractionalBits) := by
  have hw : (w.val : ℤ) < 2 * (2 : ℤ) ^ (F.integerBits + F.fractionalBits) := by
    have hpow : (2 : ℕ) ^ F.width = 2 * 2 ^ (F.integerBits + F.fractionalBits) := by
      simp [width, Nat.add_assoc, pow_add]
    have hn : w.val < 2 * 2 ^ (F.integerBits + F.fractionalBits) :=
      lt_of_lt_of_eq w.isLt hpow
    exact_mod_cast hn
  have hw0 : (0 : ℤ) ≤ w.val := Int.natCast_nonneg _
  dsimp [numerator]
  constructor <;> omega

end FixedPointFormat

/-- A finite rational weighted stencil for each requested original variable.
The offset permits the explicitly bounded base cases to return stored answers.
All general-input mode weights and rescalings are explicitly stored rationals. -/
structure WeightedDecoder (ι : Type*) (n : ℕ) where
  sampleCount : ℕ
  coordinate : Fin sampleCount → ι
  format : FixedPointFormat
  support : Fin n → Finset (Fin sampleCount)
  weight : Fin n → Fin sampleCount → ℚ
  offset : Fin n → ℚ

namespace WeightedDecoder

abbrev Messages {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n) :=
  Fin D.sampleCount → D.format.Word

def decode {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n) (w : D.Messages) : Fin n → ℚ :=
  fun i => D.offset i + ∑ j ∈ D.support i, D.weight i j * D.format.value (w j)

noncomputable def ideal {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (y : ι → ℝ) : Fin n → ℝ :=
  fun i => (D.offset i : ℝ) + ∑ j ∈ D.support i, (D.weight i j : ℝ) * y (D.coordinate j)

def Accurate {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (w : D.Messages) (y : ι → ℝ) : Prop :=
  ∀ j, |(D.format.value (w j) : ℝ) - y (D.coordinate j)| ≤
    1 / (2 : ℝ) ^ D.format.fractionalBits

def Fits {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n) (y : ι → ℝ) : Prop :=
  ∀ j, D.format.InRange (y (D.coordinate j))

/-- Exact error identity for the emitted calibration coefficients and every
finite message. No ideal physical mode is substituted for these coefficients. -/
theorem decode_error_identity {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (w : D.Messages) (y : ι → ℝ) (i : Fin n) :
    (D.decode w i : ℝ) - D.ideal y i =
      ∑ j ∈ D.support i, (D.weight i j : ℝ) *
        ((D.format.value (w j) : ℝ) - y (D.coordinate j)) := by
  simp only [decode, ideal, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
    mul_sub, Finset.sum_sub_distrib]
  ring

end WeightedDecoder

/-- All physical cells, all retained-field source entries, emitted tolerance,
and the actual finite readout coefficients are present in this finite output. -/
structure Instance (n : ℕ) where
  box : Box
  material : ScalarMaterial box.nx box.ny box.nz
  source : box.Edge → ℚ
  tolerance : ℚ
  tolerance_pos : 0 < tolerance
  decoder : WeightedDecoder box.Edge n

def Instance.dimension {n : ℕ} (I : Instance n) : ℕ := Fintype.card I.box.Edge

def Instance.cellCount {n : ℕ} (I : Instance n) : ℕ := Fintype.card I.box.Cell

noncomputable def Instance.realMatrix {n : ℕ} (I : Instance n) :
    Matrix I.box.Edge I.box.Edge ℝ :=
  (maxwell I.material).map fun q => (q : ℝ)

noncomputable def Instance.realOperator {n : ℕ} (I : Instance n) :
    EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge :=
  Matrix.toEuclideanCLM (n := I.box.Edge) (𝕜 := ℝ) I.realMatrix

noncomputable def Instance.complexMatrix {n : ℕ} (I : Instance n) :
    Matrix I.box.Edge I.box.Edge ℂ :=
  (maxwell I.material).map fun q => (q : ℂ)

noncomputable def Instance.complexOperator {n : ℕ} (I : Instance n) :
    EuclideanSpace ℂ I.box.Edge →L[ℂ] EuclideanSpace ℂ I.box.Edge :=
  Matrix.toEuclideanCLM (n := I.box.Edge) (𝕜 := ℂ) I.complexMatrix

noncomputable def Instance.complexSource {n : ℕ} (I : Instance n) :
    EuclideanSpace ℂ I.box.Edge := WithLp.toLp 2 fun e => (I.source e : ℂ)

/-- The solver may return any complex vector with the emitted relative
Euclidean residual. Its real part alone is exposed to the finite decoder. -/
def Instance.Admissible {n : ℕ} (I : Instance n) (y : EuclideanSpace ℂ I.box.Edge) : Prop :=
  ‖I.complexOperator y - I.complexSource‖ ≤ (I.tolerance : ℝ) * ‖I.complexSource‖

end Maxwell.Target
