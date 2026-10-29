import Maxwell.Composition.PhysicalGram
import Maxwell.Composition.ModeDecoder
import Maxwell.Composition.PositiveRecovery

/-! The emitted decoder samples only original source coordinates and their
fixed local defect stencil. Selection uses the actual routed coordinates,
without enumerating the full decorated graph. -/
noncomputable section
namespace Maxwell.Composition.SourcePhysicalDecoder
open scoped BigOperators
open Maxwell.Logical Maxwell.Spectral

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)

abbrev Local := Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card

def vertex (i : Fin S.n) : SourceDecoration.Vertex S precision :=
  .inl (SourceRouting.inputCoordinate S precision i)

theorem vertex_injective : Function.Injective (vertex S precision) := by
  intro i j h
  exact SourceRouting.inputCoordinate_injective S precision (Sum.inl.inj h)

def pick (ij : Fin S.n × Local P) : (PhysicalGram.box P S precision d ζ hζ hζ1).Edge :=
  (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).pick (vertex S precision ij.1,ij.2)

theorem pick_injective : Function.Injective (pick P S precision d ζ hζ hζ1 hd) := by
  intro a b h
  have he := (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).injective h
  exact Prod.ext (vertex_injective S precision (Prod.mk.inj he).1) (Prod.mk.inj he).2

def unscaled (qhat : Local P → ℚ) (v : SourceDecoration.Vertex S precision → ℚ)
    (format : Target.FixedPointFormat) : Target.WeightedDecoder
      (PhysicalGram.box P S precision d ζ hζ hζ1).Edge S.n :=
  localModeDecoder (pick P S precision d ζ hζ hζ1 hd) qhat (fun i => v (vertex S precision i)) format

def decoder (qhat : Local P → ℚ) (v : SourceDecoration.Vertex S precision → ℚ)
    (format : Target.FixedPointFormat) : Target.WeightedDecoder
      (PhysicalGram.box P S precision d ζ hζ hζ1).Edge S.n :=
  selectScaleDecoder (unscaled P S precision d ζ hζ hζ1 hd qhat v format) id
    (Normalization.sourceScale S / Normalization.matrixScale S)

variable (qhat : Local P → ℚ) (v : SourceDecoration.Vertex S precision → ℚ)
variable (format : Target.FixedPointFormat)

@[simp] theorem sampleCount :
    (decoder P S precision d ζ hζ hζ1 hd qhat v format).sampleCount = S.n*(Maxwell.Defect.ScalarDefect.edges P.defect).card := rfl

@[simp] theorem support_card (i : Fin S.n) :
    ((decoder P S precision d ζ hζ hζ1 hd qhat v format).support i).card = (Maxwell.Defect.ScalarDefect.edges P.defect).card :=
  localModeDecoder_support_card (pick P S precision d ζ hζ hζ1 hd) qhat
    (fun j => v (vertex S precision j)) format i

/-- Every finite message, including an inaccurate one, executes the exact
source rescaling already used by logical residual recovery. -/
theorem decode (w : (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Messages) :
    (decoder P S precision d ζ hζ hζ1 hd qhat v format).decode w =
      PositiveRecovery.decode S ((unscaled P S precision d ζ hζ hζ1 hd qhat v format).decode w) := by
  funext i
  exact selectScaleDecoder_decode _ id _ w i

theorem unscaled_decode (w : (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Messages)
    (i : Fin S.n) :
    (unscaled P S precision d ζ hζ hζ1 hd qhat v format).decode w i =
      v (vertex S precision i) * ∑ j, qhat j * format.value (w (finProdFinEquiv (i,j))) :=
  localModeDecoder_decode _ _ _ _ w i

@[simp] theorem accurate (w : (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Messages)
    (y : (PhysicalGram.box P S precision d ζ hζ hζ1).Edge → ℝ) :
    (decoder P S precision d ζ hζ hζ1 hd qhat v format).Accurate w y ↔
      (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Accurate w y := Iff.rfl

@[simp] theorem fits (y : (PhysicalGram.box P S precision d ζ hζ hζ1).Edge → ℝ) :
    (decoder P S precision d ζ hζ hζ1 hd qhat v format).Fits y ↔
      (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Fits y := Iff.rfl

/-- The ideal unscaled action is the selected coordinate of the actual
whole-layout block readout. -/
theorem unscaled_ideal (y : EuclideanSpace ℝ (PhysicalGram.box P S precision d ζ hζ hζ1).Edge)
    (i : Fin S.n) :
    (unscaled P S precision d ζ hζ hζ1 hd qhat v format).ideal y i =
      blockReadout (WithLp.toLp 2 fun k => (qhat k : ℝ)) (fun j => (v j : ℝ))
        (coordinateRestriction (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).pick y)
        (vertex S precision i) := by
  rw [blockReadout_apply]
  exact localModeDecoder_ideal _ _ _ _ y i

/-- Actual weighted bright coordinates of the physical field. -/
def bright (hv : ∀ j, v j ≠ 0)
    (y : EuclideanSpace ℝ (PhysicalGram.box P S precision d ζ hζ hζ1).Edge) :
    EuclideanSpace ℝ (SourceDecoration.Vertex S precision) :=
  (blockInjection P.mode).adjoint (weightedDefectCoordinates
    ((PhysicalGram.layout P S precision d ζ hζ hζ1 hd).strengthEquiv v hv)
    (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).weightEquiv
    (coordinateRestriction (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).pick) y)

theorem bright_eq (hv : ∀ j, v j ≠ 0)
    (y : EuclideanSpace ℝ (PhysicalGram.box P S precision d ζ hζ hζ1).Edge) :
    bright P S precision d ζ hζ hζ1 hd v hv y =
      blockReadout P.weightedMode (fun j => (v j : ℝ))
        (coordinateRestriction (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).pick y) := by
  have h := (PhysicalGram.layout P S precision d ζ hζ hζ1 hd).shared_readout
    (Maxwell.Defect.ScalarDefect.coordinateWeight P.defect)
    (fun i j => DecoratedDefectLayout.shared_weight S precision P.basis P.basis_injective
      P.defect d (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd) (i,j)) v hv P.mode y
  have he : weightedLocalMode (Maxwell.Defect.ScalarDefect.coordinateWeight P.defect) P.mode =
      P.weightedMode := by
    ext k
    simp [weightedLocalMode,PhysicalPlatform.weightedMode,Maxwell.Defect.sqrtWeightOperator_apply]
  simpa only [bright,he] using h

/-- Calibration error is bounded before selecting original variables; the
selection is an injective coordinate restriction and costs no dimension factor. -/
theorem unscaled_ideal_error (hv : ∀ j, v j ≠ 0)
    (y : EuclideanSpace ℝ (PhysicalGram.box P S precision d ζ hζ hζ1).Edge)
    (vmax α J cW QA ε G : ℝ)
    (hvmax : 0 < vmax) (hα : 0 < α) (hJ : 0 < J) (hcW : 0 < cW) (hQA : 0 < QA)
    (hG : 0 ≤ G) (hvb : ∀ j, |(v j : ℝ)| ≤ vmax)
    (hmode : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ)) - P.weightedMode‖ ≤
      ε / (1024*vmax*α*J*cW*QA))
    (hy : ‖y‖ ≤ 3*α*J*cW*QA*G) :
    ‖WithLp.toLp 2 ((unscaled P S precision d ζ hζ hζ1 hd qhat v format).ideal y) -
      coordinateRestriction (vertex S precision) (bright P S precision d ζ hζ hζ1 hd v hv y)‖ ≤
      3*ε*G/1024 := by
  let layout := PhysicalGram.layout P S precision d ζ hζ hζ1 hd
  let q := WithLp.toLp 2 (fun j => (qhat j : ℝ))
  have hyQ : ‖coordinateRestriction layout.pick y‖ ≤ 3*α*J*cW*QA*G := by
    calc
      _ ≤ ‖coordinateRestriction layout.pick‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right
        (coordinateRestriction_norm_le layout.pick layout.injective) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hy
  have hc := modeReadout_calibration_budget q P.weightedMode (fun j => (v j : ℝ))
    (coordinateRestriction layout.pick y) vmax α J cW QA ε G hvmax hα hJ hcW hQA hG hvb hmode hyQ
  have he : WithLp.toLp 2 ((unscaled P S precision d ζ hζ hζ1 hd qhat v format).ideal y) -
      coordinateRestriction (vertex S precision) (bright P S precision d ζ hζ hζ1 hd v hv y) =
      coordinateRestriction (vertex S precision)
        (blockReadout q (fun j => (v j : ℝ)) (coordinateRestriction layout.pick y) -
          blockReadout P.weightedMode (fun j => (v j : ℝ)) (coordinateRestriction layout.pick y)) := by
    rw [bright_eq]
    ext i
    exact congrArg (fun x => x - _) (unscaled_ideal P S precision d ζ hζ hζ1 hd qhat v format y i)
  rw [he]
  calc
    _ ≤ ‖coordinateRestriction (vertex S precision)‖ * ‖_‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖_‖ := mul_le_mul_of_nonneg_right
      (coordinateRestriction_norm_le _ (vertex_injective S precision)) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hc

/-- Every accurate fixed-width message satisfies the selected-coordinate
budget used by source recovery. The row bound follows from the calibrated
mode norm, not an independent assertion about stored decoder weights. -/
theorem finite_coordinate_error (hv : ∀ j, v j ≠ 0)
    (y : EuclideanSpace ℝ (PhysicalGram.box P S precision d ζ hζ hζ1).Edge)
    (w : (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Messages)
    (hw : (unscaled P S precision d ζ hζ hζ1 hd qhat v format).Accurate w y)
    (vmax α J cW QA ε G : ℝ)
    (hvmax : 0 < vmax) (hα : 0 < α) (hJ : 0 < J) (hcW : 0 < cW) (hQA : 0 < QA)
    (hG : 1 ≤ G) (hvb : ∀ j, 0 ≤ (v j : ℝ) ∧ (v j : ℝ) ≤ vmax)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2)
    (hmode : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ)) - P.weightedMode‖ ≤
      ε / (1024*vmax*α*J*cW*QA))
    (hy : ‖y‖ ≤ 3*α*J*cW*QA*G)
    (haccess : 2*vmax*((S.n : ℝ)*((Maxwell.Defect.ScalarDefect.edges P.defect).card : ℝ)) /
      (2 : ℝ)^format.fractionalBits ≤ ε/4096) (i : Fin S.n) :
    |((unscaled P S precision d ζ hζ hζ1 hd qhat v format).decode w i : ℝ) -
      bright P S precision d ζ hζ hζ1 hd v hv y (vertex S precision i)| ≤ 13*ε*G/4096 := by
  let D := unscaled P S precision d ζ hζ hζ1 hd qhat v format
  let k := (Maxwell.Defect.ScalarDefect.edges P.defect).card
  have hqcoord (j : Local P) : |(qhat j : ℝ)| ≤ 2 :=
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (qhat j : ℝ))) j).trans hq
  have hqsum : (∑ j : Local P, |(qhat j : ℝ)|) ≤ 2*(k : ℝ) := by
    calc
      _ ≤ ∑ _ : Local P, (2 : ℝ) := Finset.sum_le_sum (fun j _ => hqcoord j)
      _ = _ := by simp [Local,k]; ring
  have hrow : (∑ j ∈ D.support i, |(D.weight i j : ℝ)|) ≤ 2*vmax*(k : ℝ) := by
    rw [show (∑ j ∈ D.support i, |(D.weight i j : ℝ)|) =
      |(v (vertex S precision i) : ℝ)| * ∑ j, |(qhat j : ℝ)| from
      localModeDecoder_row_l1 (pick P S precision d ζ hζ hζ1 hd) qhat
        (fun i => v (vertex S precision i)) format i]
    rw [abs_of_nonneg (hvb _).1]
    calc
      _ ≤ vmax * (2*(k : ℝ)) := mul_le_mul (hvb _).2 hqsum (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hvmax.le
      _ = _ := by ring
  have hn : (1 : ℝ) ≤ S.n := by exact_mod_cast (show 1 ≤ S.n by have := i.isLt; omega)
  have hfinite : |(D.decode w i : ℝ) - D.ideal y i| ≤ ε/4096 := by
    calc
      _ ≤ (∑ j ∈ D.support i, |(D.weight i j : ℝ)|) / (2 : ℝ)^format.fractionalBits :=
        D.decode_error_le w y hw i
      _ ≤ (2*vmax*(k : ℝ)) / (2 : ℝ)^format.fractionalBits :=
        div_le_div_of_nonneg_right hrow (by positivity)
      _ ≤ (2*vmax*((S.n : ℝ)*(k : ℝ))) / (2 : ℝ)^format.fractionalBits := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [one_mul] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg k)) (show 0 ≤ 2*vmax by positivity)
      _ ≤ _ := haccess
  have hε : 0 ≤ ε := by
    have hnonneg : 0 ≤ ε/4096 := (abs_nonneg ((D.decode w i : ℝ) - D.ideal y i)).trans hfinite
    linarith
  have hcal := unscaled_ideal_error P S precision d ζ hζ hζ1 hd qhat v format hv y
    vmax α J cW QA ε G hvmax hα hJ hcW hQA (by linarith)
    (fun j => by rw [abs_of_nonneg (hvb j).1]; exact (hvb j).2) hmode hy
  have hpoint : |D.ideal y i - bright P S precision d ζ hζ hζ1 hd v hv y (vertex S precision i)| ≤
      3*ε*G/1024 := by
    exact (PiLp.norm_apply_le
      (WithLp.toLp 2 (D.ideal y) - coordinateRestriction (vertex S precision)
        (bright P S precision d ζ hζ hζ1 hd v hv y)) i).trans hcal
  calc
    _ ≤ |(D.decode w i : ℝ) - D.ideal y i| +
        |D.ideal y i - bright P S precision d ζ hζ hζ1 hd v hv y (vertex S precision i)| :=
      abs_sub_le _ _ _
    _ ≤ ε/4096 + 3*ε*G/1024 := add_le_add hfinite hpoint
    _ ≤ _ := by nlinarith

end Maxwell.Composition.SourcePhysicalDecoder
