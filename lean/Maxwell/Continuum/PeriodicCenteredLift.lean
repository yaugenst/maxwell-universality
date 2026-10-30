import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.AddCircle

/-! A continuous Banach-valued function supported in the central quarter
cube has a literal continuous periodic extension. The coordinate cut
is handled by the actual zero neighbourhood of the function. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling

open Set Filter
open scoped Topology

variable {ι E : Type*}
variable [NormedAddCommGroup E]

def centeredRepresentative (x : UnitAddTorus ι) (i : ι) : ℝ :=
  (AddCircle.equivIoc 1 (-(1/2) : ℝ) (x i)).val

theorem centeredRepresentative_mem (x : UnitAddTorus ι) (i : ι) :
    centeredRepresentative x i ∈ Ioc (-(1/2) : ℝ) (1/2 : ℝ) := by
  have h := (AddCircle.equivIoc 1 (-(1/2) : ℝ) (x i)).property
  have hu : centeredRepresentative x i ≤ -(1/2 : ℝ)+1 := h.2
  exact ⟨h.1, by linarith⟩

theorem centeredRepresentative_abs (x : UnitAddTorus ι) (i : ι) :
    |centeredRepresentative x i| ≤ 1/2 :=
  abs_le.mpr ⟨(centeredRepresentative_mem x i).1.le, (centeredRepresentative_mem x i).2⟩

theorem centeredRepresentative_coe (x : UnitAddTorus ι) (i : ι) :
    (centeredRepresentative x i : UnitAddCircle) = x i :=
  AddCircle.coe_equivIoc

theorem centeredRepresentative_norm (x : UnitAddTorus ι) (i : ι) :
    |centeredRepresentative x i| = ‖x i‖ := by
  rw [← centeredRepresentative_coe x i]
  exact ((AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
    (by simpa using centeredRepresentative_abs x i)).symm

theorem centeredRepresentative_real (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioc (-(1/2) : ℝ) (1/2 : ℝ)) :
    centeredRepresentative (fun i => (x i : UnitAddCircle)) = x := by
  funext i
  unfold centeredRepresentative
  rw [AddCircle.equivIoc_coe_eq (by simpa only [show -(1/2 : ℝ)+1 = 1/2 by norm_num] using hx i)]

def centeredLift (f : (ι → ℝ) → E) (x : UnitAddTorus ι) : E := f (centeredRepresentative x)

omit [NormedAddCommGroup E] in
theorem centeredLift_real (f : (ι → ℝ) → E) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioc (-(1/2) : ℝ) (1/2 : ℝ)) :
    centeredLift f (fun i => (x i : UnitAddCircle)) = f x := by
  rw [centeredLift, centeredRepresentative_real x hx]

theorem centeredLift_zero (f : (ι → ℝ) → E)
    (hf : ∀ x, (∃ i, (1/4 : ℝ) ≤ |x i|) → f x = 0)
    (x : UnitAddTorus ι) (hx : ∃ i, (1/4 : ℝ) ≤ ‖x i‖) : centeredLift f x = 0 := by
  apply hf
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, (centeredRepresentative_norm x i).symm ▸ hi⟩

theorem centeredLift_continuous (f : (ι → ℝ) → E) (hc : Continuous f)
    (hf : ∀ x, (∃ i, (1/4 : ℝ) ≤ |x i|) → f x = 0) : Continuous (centeredLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : ∃ i, x i = ((-(1/2) : ℝ) : UnitAddCircle)
  · obtain ⟨i, hi⟩ := hx
    have hn : ‖x i‖ = (1/2 : ℝ) := by
      rw [hi]
      have h := (AddCircle.norm_coe_eq_abs_iff 1 (x := -(1/2)) (by norm_num)).mpr (by norm_num)
      norm_num at h ⊢
    have he : ∀ᶠ y : UnitAddTorus ι in 𝓝 x, (1/4 : ℝ) < ‖y i‖ :=
      ((continuous_apply i).norm.continuousAt).eventually (lt_mem_nhds (by linarith : (1/4 : ℝ) < ‖x i‖))
    have hz : centeredLift f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [he] with y hy
      exact centeredLift_zero f hf y ⟨i, hy.le⟩
    exact continuousAt_const.congr_of_eventuallyEq hz
  · have hn : ∀ i, x i ≠ ((-(1/2) : ℝ) : UnitAddCircle) := by simpa only [not_exists] using hx
    have hr : ContinuousAt centeredRepresentative x := by
      apply continuousAt_pi.mpr
      intro i
      have hg : ContinuousAt (fun u : UnitAddCircle =>
          (AddCircle.equivIoc 1 (-(1/2) : ℝ) u).val) (x i) :=
        continuous_subtype_val.continuousAt.comp
          (AddCircle.continuousAt_equivIoc 1 (-(1/2) : ℝ) (hn i))
      exact ContinuousAt.comp (f := fun y : UnitAddTorus ι => y i) (x := x) hg
        (continuous_apply i).continuousAt
    exact hc.continuousAt.comp hr

def centeredContinuousLift (f : (ι → ℝ) → E) (hc : Continuous f)
    (hf : ∀ x, (∃ i, (1/4 : ℝ) ≤ |x i|) → f x = 0) : C(UnitAddTorus ι, E) :=
  ⟨centeredLift f, centeredLift_continuous f hc hf⟩

#print axioms centeredLift_continuous

end Maxwell.Continuum.PeriodicSampling
