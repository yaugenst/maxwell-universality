import Maxwell.Continuum.SchwartzMultiplier
import Maxwell.Continuum.FiniteWellMaterial
import Maxwell.Continuum.PeriodicMaterial

/-! Physical scalar material multiplication commutes exactly with
the compact spatial cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory Auxiliary

theorem field_commutes_scalar (θ : SchwartzMap Space ℂ) (T : FieldL2 →L[ℂ] FieldL2)
    (a : Space → ℂ) (hT : ∀ f j, T f j =ᵐ[volume] fun x => a x*f j x) (f : FieldL2) :
    field θ (T f) = T (field θ f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [field_ae θ (T f) j, hT f j, hT (field θ f) j, field_ae θ f j]
    with x hl hTf hr hθ
  rw [hl, hr, hTf, hθ]
  ring

theorem field_commutes_dielectric (θ : SchwartzMap Space ℂ) (ε : ScalarDielectric) (f : FieldL2) :
    field θ (ε.multiplier f) = ε.multiplier (field θ f) :=
  field_commutes_scalar θ ε.multiplier (fun x => (ε.coefficient x : ℂ)) ε.multiplier_ae f

theorem field_commutes_wells {ι : Type*} [Fintype ι] (θ : SchwartzMap Space ℂ)
    (h : ℝ) (r : ι → Space) (v : ι → ℝ) (f : FieldL2) :
    field θ (finiteWellOperator h r v f) = finiteWellOperator h r v (field θ f) :=
  field_commutes_scalar θ (finiteWellOperator h r v)
    (fun x => (finiteWellCoefficient h r v x : ℂ)) (finiteWellOperator_ae h r v) f

#print axioms field_commutes_wells

end Maxwell.Continuum.SchwartzMultiplier
