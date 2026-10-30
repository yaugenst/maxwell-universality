import Maxwell.Continuum.FiniteAuxiliaryH1Support
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Weak derivatives of an H¹ field supported in finitely many physical
well balls have exactly the same almost-everywhere support. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem H1Data.derivative_supported_balls {f : FieldL2} (Df : H1Data f)
    (r : ι → Space) (R : ℝ)
    (hf : ∀ k, ∀ᵐ x ∂volume, (∀ i, R ≤ ‖x-r i‖) → f k x = 0) (j k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, R ≤ ‖x-r i‖) → Df.derivative j k x = 0 := by
  let K : Set Space := ⋃ i, Metric.closedBall (r i) R
  have hK : IsClosed K := isClosed_iUnion_of_finite fun _ => Metric.isClosed_closedBall
  have hfs : ∀ k, ∀ᵐ x ∂volume, x ∉ K → f k x = 0 := by
    intro k
    filter_upwards [hf k] with x hx hnot
    apply hx
    intro i
    have hi : x ∉ Metric.closedBall (r i) R := fun hi => hnot (Set.mem_iUnion.mpr ⟨i, hi⟩)
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hi)).le
  have hds := Df.derivative_supported_closed hK hfs j k
  have hnull : ∀ᵐ x ∂(volume : Measure Space), ∀ i, x ∉ Metric.sphere (r i) R :=
    ae_all_iff.mpr fun i => measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (r i) R)
  filter_upwards [hds, hnull] with x hx hs hdist
  apply hx
  intro hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have hic : ‖x-r i‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hi
  apply hs i
  simpa only [Metric.mem_sphere, dist_eq_norm] using le_antisymm hic (hdist i)

#print axioms H1Data.derivative_supported_balls

end Maxwell.Continuum.FourierSobolev
