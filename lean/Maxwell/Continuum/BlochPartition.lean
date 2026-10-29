import Maxwell.Continuum.FourierCurl
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! The literal unit-cube/integer-alias partition of Fourier space. The
half-open cell fixes boundary representatives; measure preservation is
proved from translation invariance and the exact integer tiling. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev Alias := Fin 3 → ℤ

def integerVector (n : Alias) : Space := WithLp.toLp 2 (fun i => (n i : ℝ))

@[simp] theorem integerVector_apply (n : Alias) (i : Fin 3) :
    integerVector n i = (n i : ℝ) := rfl

scoped instance integerTranslation : AddAction Alias Space where
  vadd n x := integerVector n + x
  zero_vadd x := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext i
    change ((0 : ℤ) : ℝ) + x i = x i
    rw [Int.cast_zero, zero_add]
  add_vadd n m x := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext i
    change ((n i + m i : ℤ) : ℝ) + x i = (n i : ℝ) + ((m i : ℝ) + x i)
    rw [Int.cast_add, add_assoc]

scoped instance integerTranslation_measurable : MeasurableConstVAdd Alias Space where
  measurable_const_vadd _n := measurable_const.add measurable_id

scoped instance integerTranslation_volume : VAddInvariantMeasure Alias Space volume where
  measure_preimage_vadd n s _ := measure_preimage_add volume (integerVector n) s

def unitCell : Set Space := {x | ∀ i, 0 ≤ x i ∧ x i < 1}

theorem unitCell_measurable : MeasurableSet unitCell := by
  change MeasurableSet {x : Space | ∀ i, x i ∈ Ico (0 : ℝ) 1}
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ico.preimage
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ)))

abbrev Cell := unitCell

def cellMeasure : Measure Cell := volume.comap Subtype.val

instance cellMeasure_sigmaFinite : SigmaFinite cellMeasure := by
  apply SigmaFinite.of_map cellMeasure (f := (Subtype.val : Cell → Space))
    measurable_subtype_coe.aemeasurable
  change SigmaFinite ((volume.comap (Subtype.val : Cell → Space)).map Subtype.val)
  rw [map_comap_subtype_coe unitCell_measurable]
  infer_instance

def cellPart (x : Space) : Cell :=
  ⟨WithLp.toLp 2 (fun i => Int.fract (x i)), fun i =>
    ⟨Int.fract_nonneg (x i), Int.fract_lt_one (x i)⟩⟩

def aliasPart (x : Space) : Alias := fun i => ⌊x i⌋

/-- The exact cell-plus-alias equivalence, including every cell boundary. -/
def joinEquiv : Cell × Alias ≃ Space where
  toFun rn := integerVector rn.2 + rn.1
  invFun x := (cellPart x, aliasPart x)
  left_inv rn := by
    apply Prod.ext
    · apply Subtype.ext
      ext i
      change Int.fract ((rn.2 i : ℝ) + rn.1.val i) = rn.1.val i
      rw [Int.fract_intCast_add]
      exact Int.fract_eq_self.mpr (rn.1.property i)
    · funext i
      change ⌊(rn.2 i : ℝ) + rn.1.val i⌋ = rn.2 i
      rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr (rn.1.property i), add_zero]
  right_inv x := by
    ext i
    exact Int.floor_add_fract (x i)

theorem measurable_integerVector : Measurable integerVector := by
  exact measurable_of_countable _

theorem measurable_cellPart : Measurable cellPart := by
  apply Measurable.subtype_mk
  apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
  exact Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))).fract

theorem measurable_aliasPart : Measurable aliasPart := by
  exact Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))).floor

def join : Cell × Alias ≃ᵐ Space where
  __ := joinEquiv
  measurable_toFun := (measurable_integerVector.comp measurable_snd).add
    (measurable_subtype_coe.comp measurable_fst)
  measurable_invFun := measurable_cellPart.prodMk measurable_aliasPart

@[simp] theorem join_apply (r : Cell) (n : Alias) :
    join (r, n) = integerVector n + (r : Space) := rfl

@[simp] theorem join_symm_apply (x : Space) :
    join.symm x = (cellPart x, aliasPart x) := rfl

/-- The half-open cube is an actual integer fundamental domain. -/
theorem unitCell_fundamental : IsAddFundamentalDomain Alias unitCell volume := by
  apply IsAddFundamentalDomain.mk' unitCell_measurable.nullMeasurableSet
  intro x
  refine ⟨-aliasPart x, ?_, ?_⟩
  · intro i
    change 0 ≤ (-⌊x i⌋ : ℤ) + x i ∧ (-⌊x i⌋ : ℤ) + x i < 1
    simpa only [Int.cast_neg, Int.fract, sub_eq_add_neg, add_comm] using
      And.intro (Int.fract_nonneg (x i)) (Int.fract_lt_one (x i))
  · intro n hn
    funext i
    have hz := Int.floor_eq_zero_iff.mpr (hn i)
    change ⌊(n i : ℝ) + x i⌋ = 0 at hz
    rw [Int.floor_intCast_add] at hz
    exact eq_neg_of_add_eq_zero_left hz

/-- Regrouping Euclidean volume into the unit cell and counting measure on
all integer aliases preserves measure exactly. -/
theorem join_measurePreserving :
    MeasurePreserving join (cellMeasure.prod Measure.count) volume where
  measurable := join.measurable
  map_eq := by
    apply Measure.ext_of_lintegral volume
    intro f hf
    rw [lintegral_map_equiv]
    rw [lintegral_prod_symm (fun rn => f (join rn))
      (show AEMeasurable (fun rn => f (join rn)) _ from
        (hf.comp join.measurable).aemeasurable), lintegral_count]
    have h := unitCell_fundamental.lintegral_eq_tsum'' f
    rw [h]
    apply tsum_congr
    intro n
    exact lintegral_subtype_comap unitCell_measurable
      (fun x : Space => f (integerVector n + x))

end Maxwell.Continuum.Bloch
