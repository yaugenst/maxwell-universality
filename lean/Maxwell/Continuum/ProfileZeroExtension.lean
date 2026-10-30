import Maxwell.Continuum.ProfileAngularGevrey
import Mathlib.Topology.Piecewise

/-! A zero value and zero first derivative give a literal C1 zero extension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Filter
open scoped Topology

def zeroExtension (f : ℝ → ℝ) (t : ℝ) : ℝ := if t<1 then f t else 0

theorem zeroExtension_continuous {f : ℝ → ℝ} (hf : Continuous f) (h1 : f 1=0) :
    Continuous (zeroExtension f) := by
  change Continuous ((Iio (1 : ℝ)).piecewise f (fun _ => 0))
  apply Continuous.piecewise _ hf continuous_const
  intro x hx
  have hx1 : x=1 := by simpa only [frontier_Iio, mem_singleton_iff] using hx
  subst x
  exact h1

theorem zeroExtension_hasDerivAt {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h1 : f 1=0) (hd1 : deriv f 1=0) (t : ℝ) :
    HasDerivAt (zeroExtension f) (zeroExtension (deriv f) t) t := by
  by_cases ht : t<1
  · have he : zeroExtension f =ᶠ[𝓝 t] f := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
      exact ite_eq_left hx
    rw [zeroExtension, ite_eq_left ht]
    exact (hf t).hasDerivAt.congr_of_eventuallyEq he
  by_cases hgt : 1<t
  · have he : zeroExtension f =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with x hx
      exact ite_eq_right (not_lt_of_ge hx.le)
    rw [zeroExtension, ite_eq_right ht]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
  have heq : t=1 := by linarith
  subst t
  rw [zeroExtension, ite_eq_right (lt_irrefl (1 : ℝ))]
  have hf1 : HasDerivAt f 0 1 := by simpa only [hd1] using (hf 1).hasDerivAt
  have hl : HasDerivWithinAt (zeroExtension f) 0 (Iic (1 : ℝ)) 1 := by
    apply (hf1.hasDerivWithinAt (s := Iic (1 : ℝ))).congr_of_mem _ (by simp)
    intro x hx
    by_cases hx1 : x<1
    · exact ite_eq_left hx1
    · have he : x=1 := le_antisymm hx (le_of_not_gt hx1)
      subst x
      simp only [zeroExtension, lt_self_iff_false, ↓reduceIte, h1]
  have hr : HasDerivWithinAt (zeroExtension f) 0 (Ici (1 : ℝ)) 1 := by
    apply ((hasDerivAt_const (1 : ℝ) (0 : ℝ)).hasDerivWithinAt (s := Ici (1 : ℝ))).congr_of_mem _ (by simp)
    intro x hx
    exact ite_eq_right (not_lt_of_ge hx)
  have hu := hl.union hr
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
  exact hu

theorem zeroExtension_contDiff_one {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h1 : f 1=0) (hd1 : deriv f 1=0) : ContDiff ℝ 1 (zeroExtension f) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd (t : ℝ) := zeroExtension_hasDerivAt hdiff h1 hd1 t
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (hd t).differentiableAt
  · have he : deriv (zeroExtension f)=zeroExtension (deriv f) := funext (fun t => (hd t).deriv)
    rw [he]
    exact zeroExtension_continuous (hf.continuous_deriv le_rfl) hd1

#print axioms zeroExtension_contDiff_one

end Maxwell.Continuum.Profile
