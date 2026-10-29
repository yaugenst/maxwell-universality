import Maxwell.Composition.SelectedMaterialWidths
import Maxwell.Composition.SelectedSourceWidths
import Maxwell.Composition.SelectedDecoderWidths
import Maxwell.Composition.SelectedDyadic
import Maxwell.Composition.SelectedVolumeBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Complete every-draw resource contract for the actual selected target.
All geometry, words, local supports and decoded outputs are included. -/
noncomputable section
namespace Maxwell.Composition.SelectedResources
open Maxwell.Realization Maxwell.Composition.SelectedWidths
open Maxwell.Composition.SelectedSourceWidths Maxwell.Composition.SelectedGridWidths
open Maxwell.Composition.SelectedMaterialWidths Maxwell.Composition.SelectedDecoderWidths
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000

def coefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  1+formatCoefficient p R+materialCoefficient p R+sourceCoefficient p R+
    toleranceCoefficient p R+weightCoefficient p R+outputCoefficient p R

def constants (p : Source.Parameters) (R : SelectedPlatform) : Constants where
  overhead := SelectedVolumeBounds.overhead p R+1
  logPower := 5
  coefficientBits := coefficient p R
  conditionPower := SelectedDimensionBounds.conditionExponent p R+1
  tolerancePower := SelectedDimensionBounds.toleranceExponent p R+1
  stencilSize := localCount R
  overhead_pos := by omega
  coefficientBits_pos := by unfold coefficient; omega
  conditionPower_pos := by omega
  tolerancePower_pos := by omega

theorem short_budget {C : Constants} {S : Source.SparseSystem} {a : ℕ} {q : ℚ}
    (h : Source.ShortRational ((a*unsignedBitLength (2+S.nnz):ℕ):ℝ) q)
    (ha : a≤C.coefficientBits) : Source.ShortRational (bitBudget C S) q := by
  apply h.mono
  exact_mod_cast Nat.mul_le_mul_right (unsignedBitLength (2+S.nnz)) ha

theorem sizeBudget_log_mono (C : Constants) (S : Source.SparseSystem)
    (hm2 : 2≤S.nnz) (hlog : 5≤C.logPower) :
    sizeBudget {C with logPower:=5} S ≤ sizeBudget C S := by
  have hl : 1≤Real.log (2+(S.nnz:ℝ)) := by
    have h4 : (4:ℝ)≤2+(S.nnz:ℝ) := by exact_mod_cast (show 4≤2+S.nnz by omega)
    have h := Real.log_le_log (by norm_num : (0:ℝ)<4) h4
    have hlog4 : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rw [hlog4] at h
    linarith [Real.log_two_gt_d9]
  unfold sizeBudget
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl hlog) (by positivity)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem box_sides : 2≤((I).box R).nx ∧ 2≤((I).box R).ny ∧ 2≤((I).box R).nz := by
  constructor
  · change 2≤_+40*(_+_+2)
    omega
  constructor
  · change 2≤_+40*(_+_+2)
    omega
  · change 2≤_+40*(_+_+2)
    omega

theorem dimension_pos : 0<Fintype.card ((I).box R).Edge := by
  obtain ⟨hx,hy,hz⟩ := box_sides p S hm R
  apply Fintype.card_pos_iff.mpr
  exact ⟨Sum.inl (⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩)⟩

theorem samples_le_dimension (J : ℕ) (j : Fin J) :
    (((I).target R J j).decoder.sampleCount)≤Fintype.card ((I).box R).Edge := by
  have h := Fintype.card_le_of_injective
    (SourcePhysicalDecoder.pick R.physical S (I).precision ((I).distance R) ((I).zeta R)
      ((I).zeta_pos R) ((I).zeta_one R) ((I).distance_minimum R))
    (SourcePhysicalDecoder.pick_injective R.physical S (I).precision ((I).distance R) ((I).zeta R)
      ((I).zeta_pos R) ((I).zeta_one R) ((I).distance_minimum R))
  change S.n*(Defect.ScalarDefect.edges R.physical.defect).card≤
    Fintype.card (PhysicalGram.box R.physical S (I).precision ((I).distance R) ((I).zeta R)
      ((I).zeta_pos R) ((I).zeta_one R)).Edge
  simpa only [Fintype.card_prod,Fintype.card_fin] using h

theorem resources (C : Constants) (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (hvolume : SelectedVolumeBounds.overhead p R≤C.overhead)
    (hlog : 5≤C.logPower) (hbits : coefficient p R≤C.coefficientBits)
    (hstencil : localCount R≤C.stencilSize)
    (htolerance : SelectedDimensionBounds.toleranceExponent p R≤C.tolerancePower)
    (j : Fin (2^(I).randomBits R)) : Resources C S ((I).target R _ j) := by
  have hn := SelectedVolumeBounds.count_sizeBudget p S R {C with logPower:=5} _ hm2
    (SelectedVolumeBounds.dimension_log_bound p S hm R hm2 hp.1) hvolume rfl
  have hc := SelectedVolumeBounds.count_sizeBudget p S R {C with logPower:=5} _ hm2
    (SelectedVolumeBounds.cells_log_bound p S hm R hm2 hp.1) hvolume rfl
  have hsize := sizeBudget_log_mono C S hm2 hlog
  have hns : (Fintype.card ((I).box R).Edge:ℝ)≤sizeBudget C S := hn.trans hsize
  have hcs : (Fintype.card ((I).box R).Cell:ℝ)≤sizeBudget C S := hc.trans hsize
  have hsample0 : ((((I).target R _ j).decoder.sampleCount):ℝ)≤Fintype.card ((I).box R).Edge := by
    exact_mod_cast samples_le_dimension p S hm R _ j
  have hsample := hsample0.trans hns
  obtain ⟨hx,hy,hz⟩ := box_sides p S hm R
  refine ⟨by change 0<((I).box R).nx; omega,
    by change 0<((I).box R).ny; omega,
    by change 0<((I).box R).nz; omega,
    dimension_pos p S hm R,hns,hcs,hsample,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (format_width p S hm R hm2 hp.1).trans
      (Nat.mul_le_mul_right _ (by unfold coefficient at hbits; omega))
  · exact SelectedDyadic.material (I) R _ j
  · exact SelectedDyadic.source (I) R _ j
  · intro c
    exact short_budget (material_short p S hm R hm2 hp.1 j c)
      (by unfold coefficient at hbits; omega)
  · intro e
    exact short_budget (source_short p S hm R hm2 hp.1 hb _ j e)
      (by unfold coefficient at hbits; omega)
  · exact short_budget (tolerance_short p S hm R hm2 hp.1)
      (by unfold coefficient at hbits; omega)
  · intro i
    exact short_budget (offset_short p S hm R _ j i)
      (by unfold coefficient at hbits; omega)
  · intro i
    rw [SelectedDecoderWidths.support_card p S hm R _ j i]
    exact hstencil
  · intro i k _
    exact short_budget (weight_short p S hm R hm2 hp _ j i k)
      (by unfold coefficient at hbits; omega)
  · intro w i
    exact short_budget (output_short p S hm R hm2 hp _ j w i)
      (by unfold coefficient at hbits; omega)
  · have hm1 : (1:ℝ)≤S.nnz := by exact_mod_cast hm
    change (max 1 (S.nnz:ℝ))^(-(C.tolerancePower:ℝ))≤((I).residualTolerance R:ℝ)
    rw [max_eq_right hm1]
    exact (Real.rpow_le_rpow_of_exponent_le hm1
      (by exact_mod_cast neg_le_neg (show (SelectedDimensionBounds.toleranceExponent p R:ℝ)≤C.tolerancePower by
        exact_mod_cast htolerance))).trans
      (SelectedDimensionBounds.tolerance_bound p S hm R hm2 hp.1)

theorem selected_resources (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (j : Fin (2^(I).randomBits R)) : Resources (constants p R) S ((I).target R _ j) :=
  resources p S hm R (constants p R) hm2 hp hb (by simp [constants]) (by simp [constants])
    (by rfl) (by rfl) (by simp [constants]) j

theorem selected_success_probability (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) :
    1-3/(64*(S.nnz:ℝ))≤successProbability p (constants p R) S
      (randomBits:=(I).randomBits R) ((I).target R (2^(I).randomBits R)) :=
  SelectedDimensionBounds.success_probability p S hm R (constants p R) hm2 hp hb
    (by simp [constants])

/-- A single fixed collection of bounds works for all general inputs.
The separate finite-program theorem must still implement this constructor
and charge its execution; no machine existence is asserted here. -/
theorem fixed_resource_recovery (p : Source.Parameters) (R : SelectedPlatform) :
    ∃ C : Constants, ∀ (S : Source.SparseSystem) (hm : 0<S.nnz),
      2≤S.nnz → Source.Promises p S → S.source≠0 →
      (∀ j : Fin (2^(SelectedInput.input p S hm).randomBits R),
        Resources C S ((SelectedInput.input p S hm).target R _ j)) ∧
      1-3/(64*(S.nnz:ℝ))≤successProbability p C S
        (randomBits:=(SelectedInput.input p S hm).randomBits R)
        ((SelectedInput.input p S hm).target R (2^(SelectedInput.input p S hm).randomBits R)) := by
  refine ⟨constants p R,?_⟩
  intro S hm hm2 hp hb
  exact ⟨selected_resources p S hm R hm2 hp hb,
    selected_success_probability p S hm R hm2 hp hb⟩

end Maxwell.Composition.SelectedResources
