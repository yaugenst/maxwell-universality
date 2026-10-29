import Maxwell.Continuum.WellMultiplier

/-! Literal broad-well multiplication on full physical vector L². This is
the zero-extension realization of restriction to the well ball. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Well

def dilatedProfile (b : UnitProfile) (h : ℝ) : UnitProfile where
  coefficient x := b.coefficient (h • x)
  measurable := b.measurable.comp (measurable_const_smul h)
  nonneg x := b.nonneg (h • x)
  le_one x := b.le_one (h • x)

def fieldMultiplier (b : UnitProfile) : FieldL2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      b.multiplier.comp (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) j))

theorem fieldMultiplier_apply (b : UnitProfile) (u : FieldL2) (j : Fin 3) :
    fieldMultiplier b u j = b.multiplier (u j) := rfl

theorem fieldMultiplier_ae (b : UnitProfile) (u : FieldL2) (j : Fin 3) :
    fieldMultiplier b u j =ᵐ[volume] fun x => (b.coefficient x : ℂ) * u j x :=
  b.multiplier_ae _

theorem fieldMultiplier_norm (b : UnitProfile) (u : FieldL2) :
    ‖fieldMultiplier b u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, fieldMultiplier_apply]
  exact Finset.sum_le_sum fun j _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (b.multiplier_apply_norm_le (u j))

theorem fieldMultiplier_opNorm (b : UnitProfile) : ‖fieldMultiplier b‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using fieldMultiplier_norm b)

theorem fieldMultiplier_symmetric (b : UnitProfile) : (fieldMultiplier b).IsSymmetric := by
  intro u v
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun j _ => b.multiplier_symmetric (u j) (v j))

def Qh (h : ℝ) : FieldL2 →L[ℂ] FieldL2 := fieldMultiplier (dilatedProfile rootProfile h)

def Wh (h : ℝ) : FieldL2 →L[ℂ] FieldL2 := fieldMultiplier (dilatedProfile wellProfile h)

theorem Qh_ae (h : ℝ) (u : FieldL2) (j : Fin 3) :
    Qh h u j =ᵐ[volume] fun x => (qw (h • x) : ℂ) * u j x :=
  fieldMultiplier_ae _ _ _

theorem Wh_ae (h : ℝ) (u : FieldL2) (j : Fin 3) :
    Wh h u j =ᵐ[volume] fun x => (w (h • x) : ℂ) * u j x :=
  fieldMultiplier_ae _ _ _

theorem Qh_norm_le (h : ℝ) : ‖Qh h‖ ≤ 1 := fieldMultiplier_opNorm _

theorem Qh_selfAdjoint (h : ℝ) : IsSelfAdjoint (Qh h) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (fieldMultiplier_symmetric _)

theorem Qh_square (h : ℝ) : Qh h * Qh h = Wh h := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [Qh_ae h (Qh h u) j, Qh_ae h u j, Wh_ae h u j] with x ha hb hc
  change Qh h (Qh h u) j x = Wh h u j x
  rw [ha, hb, hc, ← mul_assoc, ← pow_two, ← Complex.ofReal_pow, qw_sq]

theorem Qh_supported {h : ℝ} (hh : 0 < h) (u : FieldL2) (j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → Qh h u j x = 0 := by
  filter_upwards [Qh_ae h u j] with x hx hnorm
  have hscaled : 1 ≤ ‖h • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hm := mul_le_mul_of_nonneg_left hnorm hh.le
    rw [mul_inv_cancel₀ hh.ne'] at hm
    exact hm
  rw [hx, (qw_zero_iff _).mpr hscaled, Complex.ofReal_zero, zero_mul]

#print axioms Qh_ae
#print axioms Qh_selfAdjoint
#print axioms Qh_square
#print axioms Qh_supported

end Maxwell.Continuum.EffectiveMass
