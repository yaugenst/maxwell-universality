import Maxwell.Target
import Maxwell.Composition.DefectCoordinates
import Maxwell.Composition.FinalReadout
import Maxwell.Composition.PhysicalReadout
import Mathlib.Logic.Equiv.Fin.Basic

/-! Concrete bounded-message decoder for rational calibrated local modes.
Every stencil coefficient is emitted explicitly and the exact ideal action
is the local dot product used in physical recovery. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

def localModeDecoder {ι : Type*} {m k : ℕ} (pick : Fin m × Fin k → ι)
    (qhat : Fin k → ℚ) (v : Fin m → ℚ) (format : Target.FixedPointFormat) :
    Target.WeightedDecoder ι m where
  sampleCount := m * k
  coordinate j := pick (finProdFinEquiv.symm j)
  format := format
  support i := Finset.univ.image fun j => finProdFinEquiv (i, j)
  weight i j := v i * qhat (finProdFinEquiv.symm j).2
  offset _ := 0

theorem localModeDecoder_support_card {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (i : Fin m) :
    ((localModeDecoder pick qhat v format).support i).card = k := by
  rw [localModeDecoder, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

/-- The rational arithmetic executed on every fixed-width message is the
finite signed local dot product, with the stored calibrated mode. -/
theorem localModeDecoder_decode {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat)
    (w : (localModeDecoder pick qhat v format).Messages) (i : Fin m) :
    (localModeDecoder pick qhat v format).decode w i =
      v i * ∑ j, qhat j * format.value (w (finProdFinEquiv (i, j))) := by
  simp only [Target.WeightedDecoder.decode, localModeDecoder, zero_add]
  rw [Finset.sum_image]
  · simp [Finset.mul_sum, mul_assoc]
  · intro a _ b _ h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

theorem localModeDecoder_ideal {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (y : ι → ℝ) (i : Fin m) :
    (localModeDecoder pick qhat v format).ideal y i =
      (v i : ℝ) * ∑ j, (qhat j : ℝ) * y (pick (i, j)) := by
  simp only [Target.WeightedDecoder.ideal, localModeDecoder, Rat.cast_zero, zero_add]
  rw [Finset.sum_image]
  · simp [Finset.mul_sum, mul_assoc]
  · intro a _ b _ h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

/-- Exact complete-vector binding to the calibrated physical readout.
This discharges the stored-decoder interpretation, without assuming it as
a premise of the residual theorem. -/
theorem localModeDecoder_ideal_eq_readout {ι : Type*} [Fintype ι] {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (y : EuclideanSpace ℝ ι) :
    WithLp.toLp 2 ((localModeDecoder pick qhat v format).ideal y) =
      blockReadout (WithLp.toLp 2 fun j => (qhat j : ℝ)) (fun i => (v i : ℝ))
        (coordinateRestriction pick y) := by
  ext i
  rw [blockReadout_apply]
  exact localModeDecoder_ideal pick qhat v format y i

theorem localModeDecoder_row_l1 {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (i : Fin m) :
    (∑ j ∈ (localModeDecoder pick qhat v format).support i,
      |((localModeDecoder pick qhat v format).weight i j : ℝ)|) =
      |(v i : ℝ)| * ∑ j, |(qhat j : ℝ)| := by
  simp only [localModeDecoder]
  rw [Finset.sum_image]
  · simp [abs_mul, Finset.mul_sum]
  · intro a _ b _ h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

/-- The emitted stored qhat coefficients obey the physical readout error
budget. The comparison target is the actual weighted defect coordinate,
not an independently postulated ideal decoder. -/
theorem localModeDecoder_physical_error {B : Target.Box} {m k : ℕ}
    {blocks : Fin m → Finset B.Cell} (layout : DefectLayout (κ := Fin k) blocks)
    (wlocal : Fin k → ℚ) (hweight : ∀ i j, layout.weight (i, j) = wlocal j)
    (qhat : Fin k → ℚ) (u : EuclideanSpace ℝ (Fin k))
    (v : Fin m → ℚ) (hv : ∀ i, v i ≠ 0) (format : Target.FixedPointFormat)
    (y : EuclideanSpace ℝ B.Edge) (vmax α J cW QA ε G : ℝ)
    (hvmax : 0 < vmax) (hα : 0 < α) (hJ : 0 < J) (hcW : 0 < cW) (hQA : 0 < QA)
    (hG : 0 ≤ G) (hvb : ∀ i, |(v i : ℝ)| ≤ vmax)
    (hmode : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ)) - weightedLocalMode wlocal u‖ ≤
      ε / (1024 * vmax * α * J * cW * QA))
    (hy : ‖y‖ ≤ 3 * α * J * cW * QA * G) :
    ‖WithLp.toLp 2 ((localModeDecoder layout.pick qhat v format).ideal y) -
      (blockInjection u).adjoint
        (weightedDefectCoordinates (layout.strengthEquiv v hv) layout.weightEquiv
          (coordinateRestriction layout.pick) y)‖ ≤ 3 * ε * G / 1024 := by
  have hyQ : ‖coordinateRestriction layout.pick y‖ ≤ 3 * α * J * cW * QA * G := by
    calc
      _ ≤ ‖coordinateRestriction layout.pick‖ * ‖y‖ :=
        (coordinateRestriction layout.pick).le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right
        (coordinateRestriction_norm_le layout.pick layout.injective) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hy
  rw [localModeDecoder_ideal_eq_readout, layout.shared_readout wlocal hweight v hv u y]
  exact modeReadout_calibration_budget (WithLp.toLp 2 (fun j => (qhat j : ℝ)))
    (weightedLocalMode wlocal u) (fun i => (v i : ℝ)) (coordinateRestriction layout.pick y)
    vmax α J cW QA ε G hvmax hα hJ hcW hQA hG hvb hmode hyQ

/-- Final original-variable selection and rational scaling are fused into
the same finite stencils. This exact identity holds even for bad draws or
inaccurate messages. -/
theorem localModeDecoder_final_decode {ι : Type*} {m k n : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (plan : Logical.DecoderPlan n m)
    (w : (localModeDecoder pick qhat v format).Messages) :
    (selectScaleDecoder (localModeDecoder pick qhat v format)
      plan.coordinate plan.scale).decode w =
      plan.decode ((localModeDecoder pick qhat v format).decode w) :=
  selected_decoder_compiles_plan _ plan w

end Maxwell.Composition
