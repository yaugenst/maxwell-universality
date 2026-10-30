import Maxwell.Continuum.ProfileFiniteMaterial
import Maxwell.Continuum.PeriodicMaterial
import Maxwell.Continuum.MaterialPerturbation

/-! The output's finite scalar dielectric and its literal ideal multiplier comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open MeasureTheory Auxiliary

variable {ι : Type*} [Fintype ι]

theorem idealWellCoefficient_continuous (h : ℝ) (r : ι → Space) (v : ι → ℝ) :
    Continuous (finiteWellCoefficient h r v) := by
  change Continuous (fun x : Space => ∑ i, v i*Well.w (h • (x-r i)))
  apply continuous_finsetSum
  intro i _
  have hi : Continuous (fun x : Space => h • (x-r i)) :=
    (continuous_id.sub continuous_const).const_smul h
  exact continuous_const.mul (Well.w_contDiff.continuous.comp hi)

variable (N : ℕ) {h : ℝ} (hh : 0<h) (r : ι → Space) (v : ι → ℝ)
  (hv0 : ∀ i, 0≤v i) (hv1 : ∀ i, v i≤1)
  (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
  (z : ℝ) (hz : |z| ≤ 1)

def encodedDielectric : ScalarDielectric where
  coefficient x := PeriodicMaterial.coefficient x+z+encodedWellCoefficient N h r v x
  measurable := ((continuous_const.add (continuous_const.mul PeriodicMaterial.periodicPotential_continuous)).add
    continuous_const |>.add (encodedWellCoefficient_continuous N h r v)).measurable
  lower x := by
    have hb := (PeriodicMaterial.coefficient_bounds x).1
    have hw := encodedWellCoefficient_nonneg N h r v hv0 x
    linarith [(abs_le.mp hz).1]
  upper x := by
    have hb := (PeriodicMaterial.coefficient_bounds x).2
    have hw := encodedWellCoefficient_bound N hh (by norm_num : (0 : ℝ)≤1) r v hv0 hv1 hdisj x
    linarith [(abs_le.mp hz).2]

theorem encodedDielectric_margin (x : Space) :
    (encodedDielectric N hh r v hv0 hv1 hdisj z hz).coefficient x ≤ 24 := by
  change PeriodicMaterial.coefficient x+z+encodedWellCoefficient N h r v x ≤ 24
  have hb := (PeriodicMaterial.coefficient_bounds x).2
  have hw := encodedWellCoefficient_bound N hh (by norm_num : (0 : ℝ)≤1) r v hv0 hv1 hdisj x
  linarith [(abs_le.mp hz).2]

def idealDielectric : ScalarDielectric where
  coefficient x := PeriodicMaterial.coefficient x+z+finiteWellCoefficient h r v x
  measurable := ((continuous_const.add (continuous_const.mul PeriodicMaterial.periodicPotential_continuous)).add
    continuous_const |>.add (idealWellCoefficient_continuous h r v)).measurable
  lower x := by
    have hb := (PeriodicMaterial.coefficient_bounds x).1
    have hw := (finiteWellCoefficient_bounds hh (by norm_num : (0 : ℝ)≤1) r v hv0 hv1 hdisj x).1
    linarith [(abs_le.mp hz).1]
  upper x := by
    have hb := (PeriodicMaterial.coefficient_bounds x).2
    have hw := (finiteWellCoefficient_bounds hh (by norm_num : (0 : ℝ)≤1) r v hv0 hv1 hdisj x).2
    linarith [(abs_le.mp hz).2]

theorem encodedDielectric_error {V : ℝ} (hV : 0≤V) (hv : ∀ i, v i≤V) (x : Space) :
    |(encodedDielectric N hh r v hv0 hv1 hdisj z hz).coefficient x-
      (idealDielectric hh r v hv0 hv1 hdisj z hz).coefficient x| ≤
      3*V*(1/2 : ℝ)^(N+24) := by
  change |(PeriodicMaterial.coefficient x+z+encodedWellCoefficient N h r v x)-
    (PeriodicMaterial.coefficient x+z+finiteWellCoefficient h r v x)| ≤ _
  rw [add_sub_add_left_eq_sub, abs_sub_comm]
  exact encodedWellCoefficient_error N hh hV r v
    (fun i => by simpa only [abs_of_nonneg (hv0 i)] using hv i) hdisj x

theorem encodedDielectric_multiplier_error {V : ℝ} (hV : 0≤V) (hv : ∀ i, v i≤V) :
    ‖(encodedDielectric N hh r v hv0 hv1 hdisj z hz).multiplier-
      (idealDielectric hh r v hv0 hv1 hdisj z hz).multiplier‖ ≤
      3*V*(1/2 : ℝ)^(N+24) :=
  ScalarDielectric.multiplier_sub_norm _ _ (by positivity)
    (encodedDielectric_error N hh r v hv0 hv1 hdisj z hz hV hv)

omit N in
theorem idealDielectric_multiplier :
    (idealDielectric hh r v hv0 hv1 hdisj z hz).multiplier=
      PeriodicMaterial.dielectric.multiplier+(z : ℂ) • ContinuousLinearMap.id ℂ FieldL2+
      finiteWellOperator h r v := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [(idealDielectric hh r v hv0 hv1 hdisj z hz).multiplier_ae f j,
    PeriodicMaterial.dielectric.multiplier_ae f j, finiteWellOperator_ae h r v f j,
    Lp.coeFn_add (PeriodicMaterial.dielectric.multiplier f j) ((z : ℂ) • f j),
    Lp.coeFn_add (PeriodicMaterial.dielectric.multiplier f j+(z : ℂ) • f j) (finiteWellOperator h r v f j),
    Lp.coeFn_smul (z : ℂ) (f j)] with x he hb hw ha ha' hs
  change (idealDielectric hh r v hv0 hv1 hdisj z hz).multiplier f j x=
    ((PeriodicMaterial.dielectric.multiplier f j+(z : ℂ) • f j)+finiteWellOperator h r v f j) x
  rw [he, ha']
  simp only [Pi.add_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs, hb, hw]
  simp only [idealDielectric, PeriodicMaterial.dielectric, Complex.ofReal_add, add_mul, Pi.smul_apply]
  rfl

#print axioms encodedDielectric_multiplier_error
#print axioms idealDielectric_multiplier

end Maxwell.Continuum.Profile
