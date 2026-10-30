import Maxwell.Continuum.EffectiveMassWell
import Maxwell.Continuum.AuxiliaryMomentumProjection

/-! The literal finite assembled dielectric well potential. Disjoint
physical well balls give the maximum-amplitude operator norm bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open MeasureTheory Bloch EffectiveMass

def translatedWellProfile (h : ℝ) (r : Space) : Well.UnitProfile where
  coefficient x := Well.w (h • (x-r))
  measurable := Well.w_contDiff.continuous.measurable.comp
    ((measurable_id.sub_const r).const_smul h)
  nonneg x := Well.w_nonneg (h • (x-r))
  le_one x := Well.w_le_one (h • (x-r))

def translatedWell (h : ℝ) (r : Space) : FieldL2 →L[ℂ] FieldL2 :=
  fieldMultiplier (translatedWellProfile h r)

theorem translatedWell_ae (h : ℝ) (r : Space) (f : FieldL2) (j : Fin 3) :
    translatedWell h r f j =ᵐ[volume] fun x => (Well.w (h • (x-r)) : ℂ) * f j x :=
  fieldMultiplier_ae _ _ _

theorem translatedWell_symmetric (h : ℝ) (r : Space) : (translatedWell h r).IsSymmetric :=
  fieldMultiplier_symmetric _

variable {ι : Type*} [Fintype ι]

def finiteWellCoefficient (h : ℝ) (r : ι → Space) (v : ι → ℝ) (x : Space) : ℝ :=
  ∑ i, v i * Well.w (h • (x-r i))

def finiteWellOperator (h : ℝ) (r : ι → Space) (v : ι → ℝ) : FieldL2 →L[ℂ] FieldL2 :=
  ∑ i, (v i : ℂ) • translatedWell h (r i)

theorem finiteWellOperator_ae (h : ℝ) (r : ι → Space) (v : ι → ℝ) (f : FieldL2) (j : Fin 3) :
    finiteWellOperator h r v f j =ᵐ[volume] fun x => (finiteWellCoefficient h r v x : ℂ) * f j x := by
  classical
  have he : finiteWellOperator h r v f j = ∑ i, (v i : ℂ) • (translatedWell h (r i) f j) := by
    simp only [finiteWellOperator, sum_apply, smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  rw [he]
  have ha (i : ι) : ((v i : ℂ) • (translatedWell h (r i) f j) : ScalarL2) =ᵐ[volume]
      fun x => (v i : ℂ) * ((Well.w (h • (x-r i)) : ℂ) * f j x) := by
    filter_upwards [Lp.coeFn_smul (v i : ℂ) (translatedWell h (r i) f j), translatedWell_ae h (r i) f j]
      with x hs hw
    rw [hs, Pi.smul_apply, hw]
    rfl
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => (v i : ℂ) • translatedWell h (r i) f j),
    ae_all_iff.mpr ha] with x hs hi
  rw [hs]
  simp only [Finset.sum_apply, hi, finiteWellCoefficient, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, mul_assoc]

theorem translatedWell_nonzero_mem_ball {h : ℝ} (hh : 0 < h) (r x : Space)
    (hw : Well.w (h • (x-r)) ≠ 0) : x ∈ Metric.ball r h⁻¹ := by
  have hn : ‖h • (x-r)‖ < 1 := lt_of_not_ge (fun hn => hw ((Well.w_zero_iff _).mpr hn))
  rw [norm_smul, Real.norm_of_nonneg hh.le] at hn
  rw [Metric.mem_ball, dist_eq_norm, inv_eq_one_div]
  exact (lt_div_iff₀ hh).mpr (by nlinarith)

theorem finiteWellCoefficient_bounds {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (x : Space) : 0 ≤ finiteWellCoefficient h r v x ∧ finiteWellCoefficient h r v x ≤ V := by
  classical
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hv0 i) (Well.w_nonneg _)
  · by_cases he : ∃ i, Well.w (h • (x-r i)) ≠ 0
    · obtain ⟨i, hi⟩ := he
      have hz (j : ι) (hji : j ≠ i) : Well.w (h • (x-r j)) = 0 := by
        by_contra hj
        exact Set.disjoint_left.mp (hdisj hji)
          (translatedWell_nonzero_mem_ball hh (r j) x hj)
          (translatedWell_nonzero_mem_ball hh (r i) x hi)
      have hsum : finiteWellCoefficient h r v x = v i * Well.w (h • (x-r i)) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hz j hji, mul_zero]
        · simp
      rw [hsum]
      exact (mul_le_of_le_one_right (hv0 i) (Well.w_le_one _)).trans (hv i)
    · have hz (i : ι) : Well.w (h • (x-r i)) = 0 := by
        by_contra hi
        exact he ⟨i, hi⟩
      simpa only [finiteWellCoefficient, hz, mul_zero, Finset.sum_const_zero] using hV

theorem finiteWellOperator_norm_le {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹)) :
    ‖finiteWellOperator h r v‖ ≤ V := by
  apply ContinuousLinearMap.opNorm_le_bound _ hV
  intro f
  have hb (j : Fin 3) : ‖finiteWellOperator h r v f j‖ ≤ V*‖f j‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [finiteWellOperator_ae h r v f j] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (finiteWellCoefficient_bounds hh hV r v hv0 hv hdisj x).1]
    exact mul_le_mul_of_nonneg_right
      (finiteWellCoefficient_bounds hh hV r v hv0 hv hdisj x).2 (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hV (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hV (norm_nonneg _))).mpr (hb j)

#print axioms finiteWellOperator_ae
#print axioms finiteWellOperator_norm_le

end Maxwell.Continuum.Auxiliary
