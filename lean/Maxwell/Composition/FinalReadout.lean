import Maxwell.Readout
import Maxwell.Logical.Decoder
import Mathlib.Tactic.Linarith

/-! Exact compilation of terminal coordinate selection and rational source
rescaling into the stored weighted decoder. The messages remain fixed-width,
and every identity holds for every bit pattern, including inaccurate messages. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

def selectScaleDecoder {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ) :
    Target.WeightedDecoder ι n where
  sampleCount := D.sampleCount
  coordinate := D.coordinate
  format := D.format
  support i := D.support (select i)
  weight i j := scale * D.weight (select i) j
  offset i := scale * D.offset (select i)

@[simp] theorem selectScaleDecoder_decode {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ)
    (w : D.Messages) (i : Fin n) :
    (selectScaleDecoder D select scale).decode w i = scale * D.decode w (select i) := by
  simp [selectScaleDecoder, Target.WeightedDecoder.decode, mul_add, Finset.mul_sum, mul_assoc]

@[simp] theorem selectScaleDecoder_ideal {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ)
    (y : ι → ℝ) (i : Fin n) :
    (selectScaleDecoder D select scale).ideal y i = (scale : ℝ) * D.ideal y (select i) := by
  simp [selectScaleDecoder, Target.WeightedDecoder.ideal, mul_add, Finset.mul_sum, mul_assoc]

@[simp] theorem selectScaleDecoder_accurate {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ)
    (w : D.Messages) (y : ι → ℝ) :
    (selectScaleDecoder D select scale).Accurate w y ↔ D.Accurate w y := Iff.rfl

@[simp] theorem selectScaleDecoder_fits {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ)
    (y : ι → ℝ) :
    (selectScaleDecoder D select scale).Fits y ↔ D.Fits y := Iff.rfl

theorem selectScaleDecoder_row_bound {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m) (scale : ℚ)
    (W : ℝ) (hrow : ∀ i, ∑ j ∈ D.support i, |(D.weight i j : ℝ)| ≤ W) :
    ∀ i, ∑ j ∈ (selectScaleDecoder D select scale).support i,
      |((selectScaleDecoder D select scale).weight i j : ℝ)| ≤ |(scale : ℝ)| * W := by
  intro i
  simpa [selectScaleDecoder, abs_mul, ← Finset.mul_sum] using
    mul_le_mul_of_nonneg_left (hrow (select i)) (abs_nonneg (scale : ℝ))

def selectCoordinates {m n : ℕ} (select : Fin n → Fin m)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => x (select i)

/-- Selecting distinct original coordinates is contractive in the actual
Euclidean norm; no dimension factor is paid during final decoding. -/
theorem selectCoordinates_norm_le {m n : ℕ} (select : Fin n → Fin m)
    (hinj : Function.Injective select) (x : EuclideanSpace ℝ (Fin m)) :
    ‖selectCoordinates select x‖ ≤ ‖x‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  change ∑ i, x (select i) ^ 2 ≤ ∑ j, x j ^ 2
  calc
    ∑ i, x (select i) ^ 2 = ∑ j ∈ Finset.univ.image select, x j ^ 2 := by
      rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    _ ≤ ∑ j, x j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)

/-- The actual emitted final rational weights implement the selected and
rescaled terminal answer exactly on every finite input message. -/
theorem selectScaleDecoder_error_le {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m)
    (hinj : Function.Injective select) (scale : ℚ) (w : D.Messages)
    (z : EuclideanSpace ℝ (Fin m)) :
    ‖WithLp.toLp 2 (fun i => ((selectScaleDecoder D select scale).decode w i : ℝ)) -
      (scale : ℝ) • selectCoordinates select z‖ ≤
        |(scale : ℝ)| * ‖WithLp.toLp 2 (fun i => (D.decode w i : ℝ)) - z‖ := by
  have hid : WithLp.toLp 2
      (fun i => ((selectScaleDecoder D select scale).decode w i : ℝ)) -
      (scale : ℝ) • selectCoordinates select z =
      (scale : ℝ) • selectCoordinates select
        (WithLp.toLp 2 (fun i => (D.decode w i : ℝ)) - z) := by
    ext i
    simp [selectCoordinates, mul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (selectCoordinates_norm_le select hinj _) (abs_nonneg _)

theorem selectScaleDecoder_ideal_error_le {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (select : Fin n → Fin m)
    (hinj : Function.Injective select) (scale : ℚ) (y : ι → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) :
    ‖WithLp.toLp 2 ((selectScaleDecoder D select scale).ideal y) -
      (scale : ℝ) • selectCoordinates select z‖ ≤
        |(scale : ℝ)| * ‖WithLp.toLp 2 (D.ideal y) - z‖ := by
  have hid : WithLp.toLp 2 ((selectScaleDecoder D select scale).ideal y) -
      (scale : ℝ) • selectCoordinates select z =
      (scale : ℝ) • selectCoordinates select (WithLp.toLp 2 (D.ideal y) - z) := by
    ext i
    simp [selectCoordinates, mul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (selectCoordinates_norm_le select hinj _) (abs_nonneg _)

/-- Binding to the logical compiler's authoritative decoder-plan type.
The final target stencils implement that plan exactly without materializing
an additional unbounded intermediate solver message. -/
theorem selected_decoder_compiles_plan {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (plan : Logical.DecoderPlan n m)
    (w : D.Messages) :
    (selectScaleDecoder D plan.coordinate plan.scale).decode w =
      plan.decode (D.decode w) := by
  funext i
  exact selectScaleDecoder_decode D plan.coordinate plan.scale w i

theorem selected_decoder_ideal_compiles_plan {ι : Type*} {m n : ℕ}
    (D : Target.WeightedDecoder ι m) (plan : Logical.DecoderPlan n m)
    (y : ι → ℝ) :
    WithLp.toLp 2 ((selectScaleDecoder D plan.coordinate plan.scale).ideal y) =
      plan.realDecode (WithLp.toLp 2 (D.ideal y)) := by
  ext i
  exact selectScaleDecoder_ideal D plan.coordinate plan.scale y i

end Maxwell.Composition
