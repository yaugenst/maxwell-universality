import Maxwell.Continuum.BoxModesCutoffTest
import Maxwell.Continuum.BoxModesL2Convergence

/-! Actual L² representatives of the box modes and Cartesian derivatives. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory
open scoped Topology ContDiff BigOperators

theorem contDiff_scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    ContDiff ℝ ∞ (scalarBoxMode N ν c) := by
  apply contDiff_prod
  intro j _
  exact (contDiff_coordinateMode N ν c j).comp
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff

theorem abs_scalarBoxMode_le_one (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (x : Point) : |scalarBoxMode N ν c x| ≤ 1 := by
  rw [scalarBoxMode, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    (fun j _ => abs_coordinateMode_le_one N ν c j (x j))

theorem abs_partial_scalarBoxMode_le (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) (x : Point) :
    |partialDeriv (scalarBoxMode N ν c) j x| ≤ |(ν j : ℝ) * Real.pi / N j| := by
  change |partialDeriv (fun y => ∏ k, coordinateMode N ν c k (y k)) j x| ≤ _
  rw [partial_separated_product _
    (fun k => (contDiff_coordinateMode N ν c k).differentiable (by simp)), abs_mul]
  have hp : |∏ k ∈ Finset.univ.erase j, coordinateMode N ν c k (x k)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun k _ => abs_coordinateMode_le_one N ν c k (x k))
  exact (mul_le_mul (abs_deriv_coordinateMode_le N ν c j (x j)) hp
    (abs_nonneg _) (abs_nonneg _)).trans_eq (mul_one _)

theorem continuous_partial_scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) : Continuous (fun x => partialDeriv (scalarBoxMode N ν c) j x) :=
  ((contDiff_scalarBoxMode N ν c).continuous_fderiv (by simp)).clm_apply continuous_const

theorem memLp_complex_partial_scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) : MemLp (fun x => (partialDeriv (scalarBoxMode N ν c) j x : ℂ)) 2
      (volume.restrict (openBox N)) := by
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.comp (continuous_partial_scalarBoxMode N ν c j)).aestronglyMeasurable)
    |(ν j : ℝ) * Real.pi / N j|
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using abs_partial_scalarBoxMode_le N ν c j x

def zeroExtendedBoxPartial (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) : ScalarL2 :=
  MemLp.toLp ((openBox N).indicator (fun x => (partialDeriv (scalarBoxMode N ν c) j x : ℂ)))
    ((memLp_indicator_iff_restrict (isOpen_openBox N).measurableSet).mpr
      (memLp_complex_partial_scalarBoxMode N ν c j))

theorem zeroExtendedBoxPartial_coe_ae (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) :
    (zeroExtendedBoxPartial N ν c j : Space → ℂ) =ᵐ[volume]
      (openBox N).indicator (fun x => (partialDeriv (scalarBoxMode N ν c) j x : ℂ)) :=
  MemLp.coeFn_toLp _

def cutoffScalarSchwartz (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) (n : ℕ) :
    SchwartzMap Space ℂ :=
  testSchwartz (boxDomain N) (cutoffTestScalar N ν c (cutoffWidth n) (cutoffWidth_pos n))

def cutoffScalarL2 (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) (n : ℕ) : ScalarL2 :=
  (cutoffScalarSchwartz N ν c n).toLp 2 volume

def cutoffPartialL2 (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) (n : ℕ) : ScalarL2 :=
  (partialSchwartz j (cutoffScalarSchwartz N ν c n)).toLp 2 volume

theorem cutoffScalarL2_coe_ae (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) (n : ℕ) :
    (cutoffScalarL2 N ν c n : Space → ℂ) =ᵐ[volume]
      fun x => (cutoffScalarMode N ν c (cutoffWidth n) x : ℂ) :=
  (cutoffScalarSchwartz N ν c n).coeFn_toLp 2 volume

theorem cutoffPartialL2_coe_ae (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) (n : ℕ) :
    (cutoffPartialL2 N ν c j n : Space → ℂ) =ᵐ[volume]
      fun x => (partialDeriv (cutoffScalarMode N ν c (cutoffWidth n)) j x : ℂ) := by
  filter_upwards [(partialSchwartz j (cutoffScalarSchwartz N ν c n)).coeFn_toLp 2 volume]
    with x hx
  exact hx.trans (partialSchwartz_cutoffTestScalar N ν c j _ _ x)

theorem cutoffScalarL2_bound (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) (n : ℕ) :
    ∀ᵐ x ∂volume, ‖cutoffScalarL2 N ν c n x‖ ≤ (openBox N).indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [cutoffScalarL2_coe_ae N ν c n] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs]
  by_cases hΩ : x ∈ openBox N
  · rw [Set.indicator_of_mem hΩ]
    exact abs_cutoffScalarMode_le_one N ν c _ x
  · rw [Set.indicator_of_notMem hΩ,
      cutoffScalarMode_eq_zero_outside N ν c (cutoffWidth_pos n) hΩ, abs_zero]

theorem zeroExtendedBoxMode_bound (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    ∀ᵐ x ∂volume, ‖zeroExtendedBoxMode N c ν x‖ ≤ (openBox N).indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [zeroExtendedBoxMode_coe_ae N c ν] with x hx
  rw [hx]
  by_cases hΩ : x ∈ openBox N
  · rw [Set.indicator_of_mem hΩ, Set.indicator_of_mem hΩ, Complex.norm_real, Real.norm_eq_abs]
    exact abs_scalarBoxMode_le_one N ν c x
  · rw [Set.indicator_of_notMem hΩ, Set.indicator_of_notMem hΩ, norm_zero]

theorem cutoffPartialL2_bound (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c j : Fin 3) (hj : j ≠ c)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C) (n : ℕ) :
    ∀ᵐ x ∂volume, ‖cutoffPartialL2 N ν c j n x‖ ≤
      (openBox N).indicator (fun _ => (4 * C + 1) * |(ν j : ℝ) * Real.pi / N j|) x := by
  filter_upwards [cutoffPartialL2_coe_ae N ν c j n] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs]
  by_cases hΩ : x ∈ openBox N
  · rw [Set.indicator_of_mem hΩ]
    exact abs_partial_cutoffScalarMode_le N hN ν c j hj C hC hD (cutoffWidth_pos n) x
  · rw [Set.indicator_of_notMem hΩ,
      partial_cutoffScalarMode_eq_zero_outside N ν c j (cutoffWidth_pos n) hΩ, abs_zero]

theorem zeroExtendedBoxPartial_bound (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᵐ x ∂volume, ‖zeroExtendedBoxPartial N ν c j x‖ ≤
      (openBox N).indicator (fun _ => (4 * C + 1) * |(ν j : ℝ) * Real.pi / N j|) x := by
  filter_upwards [zeroExtendedBoxPartial_coe_ae N ν c j] with x hx
  rw [hx]
  by_cases hΩ : x ∈ openBox N
  · rw [Set.indicator_of_mem hΩ, Set.indicator_of_mem hΩ, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_partial_scalarBoxMode_le N ν c j x).trans
      (le_mul_of_one_le_left (abs_nonneg _) (by linarith))
  · rw [Set.indicator_of_notMem hΩ, Set.indicator_of_notMem hΩ, norm_zero]

/-- The scalar field part of the actual compact smooth test sequence converges
in global L² to the zero-extended physical mode. -/
theorem cutoffScalarL2_tendsto (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    Tendsto (cutoffScalarL2 N ν c) atTop (𝓝 (zeroExtendedBoxMode N c ν)) := by
  apply tendsto_L2_of_ae_eventually_eq volume _ _
    ((openBox N).indicator (fun _ => (1 : ℝ))) (square_integrable_box_bound N 1)
    (cutoffScalarL2_bound N ν c) (zeroExtendedBoxMode_bound N ν c)
  filter_upwards [ae_all_iff.mpr (cutoffScalarL2_coe_ae N ν c),
    zeroExtendedBoxMode_coe_ae N c ν] with x hseq hlim
  filter_upwards [cutoffScalarMode_eventually_eq N ν c x] with n hn
  rw [hseq n, hlim, hn]
  by_cases hx : x ∈ openBox N <;> simp [Set.indicator, hx]

/-- Every tangential Cartesian derivative converges in global L². The
normal derivative is intentionally excluded because PEC imposes no normal trace. -/
theorem cutoffPartialL2_tendsto (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c j : Fin 3) (hj : j ≠ c) :
    Tendsto (cutoffPartialL2 N ν c j) atTop (𝓝 (zeroExtendedBoxPartial N ν c j)) := by
  obtain ⟨C, hC, hD⟩ := transition_deriv_bound
  apply tendsto_L2_of_ae_eventually_eq volume _ _
    ((openBox N).indicator (fun _ => (4 * C + 1) * |(ν j : ℝ) * Real.pi / N j|))
    (square_integrable_box_bound N _)
    (cutoffPartialL2_bound N hN ν c j hj C hC.le hD)
    (zeroExtendedBoxPartial_bound N ν c j C hC.le)
  filter_upwards [ae_all_iff.mpr (cutoffPartialL2_coe_ae N ν c j),
    zeroExtendedBoxPartial_coe_ae N ν c j] with x hseq hlim
  filter_upwards [partial_cutoffScalarMode_eventually_eq N ν c j x] with n hn
  rw [hseq n, hlim, hn]
  by_cases hx : x ∈ openBox N <;> simp [Set.indicator, hx]

#print axioms cutoffScalarL2_tendsto
#print axioms cutoffPartialL2_tendsto

end Maxwell.Continuum.BoxModes
