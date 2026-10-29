import Maxwell.Green.Contour
import Mathlib.MeasureTheory.Integral.Pi

/-! Periodic coordinate cancellation on an actual finite-dimensional cube. -/

open MeasureTheory Set

namespace Maxwell.Green

theorem periodic_pi_flux_integral_eq_zero {n : ℕ} (i : Fin (n + 1))
    {f f' : (Fin (n + 1) → ℝ) → ℂ} {a p : ℝ} (hp : 0 ≤ p)
    (hderiv : ∀ (q : Fin n → ℝ) x, x ∈ uIcc a (a + p) →
      HasDerivAt (fun x => f (i.insertNth x q)) (f' (i.insertNth x q)) x)
    (hint : Integrable f' (Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Ioc a (a + p)))))
    (hperiod : ∀ q : Fin n → ℝ, f (i.insertNth (a + p) q) = f (i.insertNth a q)) :
    (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Ioc a (a + p))))) = 0 := by
  let μ : Measure ℝ := volume.restrict (Ioc a (a + p))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hm : MeasurePreserving e (Measure.pi (fun _ => μ))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := measurePreserving_piFinSuccAbove (fun _ => μ) i
  have hi : Integrable (fun z : ℝ × (Fin n → ℝ) => f' (i.insertNth z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    have h := (hm.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).2 hint
    simpa only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] using h
  have heq : (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => μ))) =
      ∫ z : ℝ × (Fin n → ℝ), f' (i.insertNth z.1 z.2)
        ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    rw [← hm.symm.integral_comp']
    rfl
  change (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => μ))) = 0
  rw [heq]
  exact periodic_flux_integral_eq_zero hp hderiv hi hperiod

theorem periodic_pi_flux_integral_eq_zero_ae {n : ℕ} (i : Fin (n + 1))
    {f f' : (Fin (n + 1) → ℝ) → ℂ} {a p : ℝ} (hp : 0 ≤ p)
    (hderiv : ∀ᵐ q ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioc a (a + p)))),
      ∀ x ∈ uIcc a (a + p),
        HasDerivAt (fun x => f (i.insertNth x q)) (f' (i.insertNth x q)) x)
    (hint : Integrable f' (Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Ioc a (a + p)))))
    (hperiod : ∀ᵐ q ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioc a (a + p)))),
      f (i.insertNth (a + p) q) = f (i.insertNth a q)) :
    (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Ioc a (a + p))))) = 0 := by
  let μ : Measure ℝ := volume.restrict (Ioc a (a + p))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hm : MeasurePreserving e (Measure.pi (fun _ => μ))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := measurePreserving_piFinSuccAbove (fun _ => μ) i
  have hi : Integrable (fun z : ℝ × (Fin n → ℝ) => f' (i.insertNth z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    have h := (hm.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).2 hint
    simpa only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] using h
  have heq : (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => μ))) =
      ∫ z : ℝ × (Fin n → ℝ), f' (i.insertNth z.1 z.2)
        ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    rw [← hm.symm.integral_comp']
    rfl
  change (∫ q, f' q ∂(Measure.pi (fun _ : Fin (n + 1) => μ))) = 0
  rw [heq]
  exact periodic_flux_integral_eq_zero_ae hp hderiv hi hperiod

end Maxwell.Green
