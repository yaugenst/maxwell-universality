import Maxwell.Continuum.FourierConjugation
import Maxwell.Continuum.CellBandFourierReversal
import Maxwell.Continuum.FiberNormalizationStar

/-! Exact physical conjugation under the genuine unitary Bloch transform.
Frequency negation is transported through the proved cell/alias equivalence,
so the half-open boundary representatives are included in the formula. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory CellBandFourier FiberNormalization

def negativeFrequency : QuasiCell × Alias ≃ᵐ QuasiCell × Alias :=
  (quasiFrequencyJoin.trans (MeasurableEquiv.neg Space)).trans quasiFrequencyJoin.symm

theorem negativeFrequency_measurePreserving :
    MeasurePreserving negativeFrequency (quasiMeasure.prod Measure.count)
      (quasiMeasure.prod Measure.count) :=
  quasiFrequencyJoin_measurePreserving.symm.comp
    ((Measure.measurePreserving_neg volume).comp quasiFrequencyJoin_measurePreserving)

@[simp] theorem join_negativeFrequency (qn : QuasiCell × Alias) :
    quasiFrequencyJoin (negativeFrequency qn) = -quasiFrequencyJoin qn :=
  quasiFrequencyJoin.apply_symm_apply _

theorem negativeFrequency_involutive (qn : QuasiCell × Alias) :
    negativeFrequency (negativeFrequency qn) = qn := by
  apply quasiFrequencyJoin.injective
  rw [join_negativeFrequency, join_negativeFrequency, neg_neg]

theorem product_ae_fst {p : QuasiCell → Prop} (h : ∀ᵐ q ∂quasiMeasure, p q) :
    ∀ᵐ qn ∂quasiMeasure.prod (Measure.count : Measure Alias), p qn.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

theorem negativeFrequency_fst_ae {p : QuasiCell → Prop}
    (h : ∀ᵐ q ∂quasiMeasure, p q) :
    ∀ᵐ qn ∂quasiMeasure.prod Measure.count, p (negativeFrequency qn).1 :=
  negativeFrequency_measurePreserving.quasiMeasurePreserving.ae (product_ae_fst h)

/-- Exact product-space formula, also including the cell faces. -/
theorem unitary_conjugation_pair_ae (f : FieldL2) :
    ∀ᵐ qn ∂quasiMeasure.prod Measure.count, ∀ i : Fin 3,
      unitary (fieldConjugation f) qn.1 qn.2 i =
        star (unitary f (negativeFrequency qn).1 (negativeFrequency qn).2 i) := by
  have hF := ae_all_iff.mpr fun i : Fin 3 =>
    quasiFrequencyJoin_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (fieldFourier_conjugation_ae f i)
  filter_upwards [product_ae_fst (unitary_coordinate_ae (fieldConjugation f)),
    negativeFrequency_fst_ae (unitary_coordinate_ae f), hF] with qn hc hf hF
  intro i
  rw [hc qn.2 i, hf (negativeFrequency qn).2 i, join_negativeFrequency]
  exact hF i

def negativeCell (q : QuasiCell) (hq : ∀ j, -Real.pi / 2 < q.val j) : QuasiCell :=
  ⟨-q.val, fun j => by
    change -Real.pi / 2 ≤ -q.val j ∧ -q.val j < Real.pi / 2
    have hj := q.property j
    have h := hq j
    constructor <;> linarith⟩

@[simp] theorem negativeCell_val (q : QuasiCell) (hq : ∀ j, -Real.pi / 2 < q.val j) :
    (negativeCell q hq).val = -q.val := rfl

theorem negativeFrequency_interior (q : QuasiCell)
    (hq : ∀ j, -Real.pi / 2 < q.val j) (n : Alias) :
    negativeFrequency (q, n) = (negativeCell q hq, reverseAlias n) := by
  apply quasiFrequencyJoin.injective
  rw [join_negativeFrequency]
  apply PiLp.ext
  intro j
  simp only [PiLp.neg_apply, quasiFrequencyJoin_apply, negativeCell_val]
  change -((q.val j + Real.pi / 2 + Real.pi * (n j : ℝ)) / (2 * Real.pi)) =
    (-q.val j + Real.pi / 2 + Real.pi * ((-n j - 1 : ℤ) : ℝ)) / (2 * Real.pi)
  push_cast
  ring

/-- On the open cell the exact formula becomes full alias reversal and
coefficient conjugation, without any truncation of the fiber. -/
theorem unitary_conjugation_interior_ae (f : FieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ hq : (∀ j, -Real.pi / 2 < q.val j),
      unitary (fieldConjugation f) q = reversal (star (unitary f (negativeCell q hq))) := by
  filter_upwards [product_ae_all_alias (unitary_conjugation_pair_ae f)] with q hq
  intro hi
  apply lp.ext
  funext n
  apply PiLp.ext
  intro j
  have h := hq n j
  rw [negativeFrequency_interior q hi n] at h
  simpa only [reversal_apply, fiber_star_apply, polarization_star_apply] using h

end Maxwell.Continuum.Bloch
