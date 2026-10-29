import Maxwell.Continuum.CellSpatialTiling

/-! Finite collections of actual cell indicators are orthogonal
projections. Their squared component norms obey the exact L² identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier Bloch MeasureTheory Set
open scoped InnerProduct

def familyProjection (F : Finset Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  ∑ a ∈ F, cellProjection a

theorem familyProjection_apply (F : Finset Bloch.Alias) (f : FieldL2) :
    familyProjection F f = ∑ a ∈ F, cellProjection a f := by
  simp only [familyProjection, ContinuousLinearMap.sum_apply]

theorem familyProjection_ae (F : Finset Bloch.Alias) (f : FieldL2) (j : Fin 3) :
    familyProjection F f j =ᵐ[volume] fun x => if cellIndex x ∈ F then f j x else 0 := by
  classical
  have he : familyProjection F f j = ∑ a ∈ F, cellProjection a f j := by
    rw [familyProjection_apply]
    exact (map_sum (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) j) (fun a => cellProjection a f) F)
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum F (fun a => cellProjection a f j),
    ae_all_iff.mpr (fun a : Bloch.Alias => cellProjection_ae a f j)] with x hsum hcell
  rw [hsum]
  change (∑ a ∈ F, cellProjection a f j x) = _
  have ht (a : Bloch.Alias) : cellProjection a f j x = if cellIndex x = a then f j x else 0 := by
    rw [hcell a]
    simp only [Set.indicator_apply, spatialBox_iff_index]
  simp_rw [ht]
  exact Finset.sum_ite_eq F (cellIndex x) (fun _ => f j x)

theorem familyProjection_apply_norm_le (F : Finset Bloch.Alias) (f : FieldL2) :
    ‖familyProjection F f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [familyProjection_ae F f j] with x hx
  rw [hx]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f j x)

theorem familyProjection_norm_le (F : Finset Bloch.Alias) : ‖familyProjection F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using familyProjection_apply_norm_le F f

theorem cellProjection_orthogonal {a b : Bloch.Alias} (hab : a ≠ b) (f g : FieldL2) :
    inner ℂ (cellProjection a f) (cellProjection b g) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [cellProjection_ae a f j, cellProjection_ae b g j] with x ha hb
  rw [ha, hb]
  by_cases hx : x ∈ spatialBox a
  · have hy : x ∉ spatialBox b := fun h => Set.disjoint_left.mp (spatialBox_disjoint hab) hx h
    rw [indicator_of_notMem hy, inner_zero_right]
  · rw [indicator_of_notMem hx, inner_zero_left]

theorem familyProjection_norm_sq (F : Finset Bloch.Alias) (f : FieldL2) :
    ‖familyProjection F f‖^2 = ∑ a ∈ F, ‖cellProjection a f‖^2 := by
  classical
  have hi : inner ℂ (familyProjection F f) (familyProjection F f) =
      ∑ a ∈ F, inner ℂ (cellProjection a f) (cellProjection a f) := by
    rw [familyProjection_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro a ha
    rw [inner_sum]
    apply Finset.sum_eq_single a
    · intro b _ hba
      exact cellProjection_orthogonal hba.symm f f
    · exact fun h => False.elim (h ha)
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hi, Complex.re_sum]
  exact Finset.sum_congr rfl fun _ _ => (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem familyProjection_sum_norm_sq_le (F : Finset Bloch.Alias) (f : FieldL2) :
    (∑ a ∈ F, ‖cellProjection a f‖^2) ≤ ‖f‖^2 := by
  rw [← familyProjection_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (familyProjection_apply_norm_le F f) 2

theorem familyProjection_sum_norm_le (F : Finset Bloch.Alias) (f : FieldL2) :
    (∑ a ∈ F, ‖cellProjection a f‖) ≤ Real.sqrt (F.card : ℝ) * ‖f‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq F (fun a => ‖cellProjection a f‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hb := familyProjection_sum_norm_sq_le F f
  have hc : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hr := Real.sq_sqrt hc
  have hm := mul_le_mul_of_nonneg_right hb hc
  have hn : 0 ≤ ∑ a ∈ F, ‖cellProjection a f‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [Real.sqrt_nonneg (F.card : ℝ), norm_nonneg f,
    sq_nonneg (Real.sqrt (F.card : ℝ) * ‖f‖)]

#print axioms familyProjection_ae
#print axioms familyProjection_sum_norm_le

end Maxwell.Continuum.CellGauge
