import Maxwell.Continuum.BoxModesSpectrum
import Maxwell.Continuum.InvariantRestriction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual finite low-frequency transverse space and its polarization count. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators InnerProductSpace

def projectedAmplitudeMap (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) :
    (Fin 3 → ℂ) →ₗ[ℂ] transverseSpace (boxDomain N) :=
  (transverseProjection (boxDomain N)).toLinearMap.comp (boxAmplitudeMap N ν)

theorem projectedAmplitudeMap_momentum_zero (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) :
    projectedAmplitudeMap N ν (fun j => (integerWaveNumber N ν j : ℂ)) = 0 := by
  exact (gradientSpace (boxDomain N)).orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (longitudinalMode_mem_kernel N hN ν)

theorem scalarBoxMode_zero_frequency (N : Fin 3 → ℝ) (c : Fin 3) :
    scalarBoxMode N 0 c = 0 := by
  funext x
  fin_cases c <;> simp [scalarBoxMode, coordinateMode, intervalCos, intervalSin,
    Fin.prod_univ_three]

theorem zeroExtendedBoxMode_zero_frequency (N : Fin 3 → ℝ) (c : Fin 3) :
    zeroExtendedBoxMode N c 0 = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [zeroExtendedBoxMode_coe_ae N c 0,
    MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (MeasureTheory.volume : MeasureTheory.Measure Space))]
    with x hx hz
  rw [hx, hz, scalarBoxMode_zero_frequency]
  simp

theorem projectedAmplitudeMap_zero_frequency (N : Fin 3 → ℝ) :
    projectedAmplitudeMap N 0 = 0 := by
  apply LinearMap.ext
  intro a
  change transverseProjection (boxDomain N) (boxAmplitude N 0 a) = 0
  have hzero : boxAmplitude N 0 a = 0 := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change a j • zeroExtendedBoxMode N j 0 = 0
    rw [zeroExtendedBoxMode_zero_frequency, smul_zero]
  rw [hzero, map_zero]

theorem integerWaveNumber_ne_zero (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (hν : ν ≠ 0) :
    (fun j => (integerWaveNumber N ν j : ℂ)) ≠ 0 := by
  intro hz
  apply hν
  funext j
  have hp : integerWaveNumber N ν j = 0 := by
    have he : (integerWaveNumber N ν j : ℂ) = 0 := congrFun hz j
    exact Complex.ofReal_eq_zero.mp he
  have hm := congrArg (fun t : ℝ => t * N j) hp
  change ((ν j : ℝ) * Real.pi / N j) * N j = 0 * N j at hm
  rw [div_mul_cancel₀ _ (ne_of_gt (hN j)), zero_mul] at hm
  have hn := (mul_eq_zero.mp hm).resolve_right Real.pi_ne_zero
  exact_mod_cast hn

theorem projectedAmplitudeMap_finrank_le (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) :
    Module.finrank ℂ (projectedAmplitudeMap N ν).range ≤ 2 := by
  by_cases hν : ν = 0
  · rw [hν, projectedAmplitudeMap_zero_frequency, LinearMap.range_zero, finrank_bot]
    norm_num
  · have hp := integerWaveNumber_ne_zero N hN ν hν
    have hk : Submodule.span ℂ {fun j => (integerWaveNumber N ν j : ℂ)} ≤
        (projectedAmplitudeMap N ν).ker := by
      apply Submodule.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact projectedAmplitudeMap_momentum_zero N hN ν
    have hd := Submodule.finrank_mono hk
    rw [finrank_span_singleton hp] at hd
    have hr := LinearMap.finrank_range_add_finrank_ker (projectedAmplitudeMap N ν)
    norm_num at hr
    omega

def lowTransverseSpace (N : ModeCount.BoxLengths) :
    Submodule ℂ (transverseSpace (boxDomain (fun j => (N j : ℝ)))) :=
  ⨆ ν : ModeCount.LowFrequency N,
    (projectedAmplitudeMap (fun j => (N j : ℝ)) (fun j => (ν.val j : ℤ))).range

theorem lowTransverseSpace_finiteDimensional (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    FiniteDimensional ℂ (lowTransverseSpace N) := by
  let _ := ModeCount.finite_lowFrequency N hN
  unfold lowTransverseSpace
  infer_instance

theorem finrank_iSup_le_sum {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℂ H]
    (S : ι → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (S i)] :
    Module.finrank ℂ (⨆ i, S i : Submodule ℂ H) ≤ ∑ i, Module.finrank ℂ (S i) := by
  classical
  have hfin (s : Finset ι) :
      Module.finrank ℂ (s.sup S : Submodule ℂ H) ≤ ∑ i ∈ s, Module.finrank ℂ (S i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)
  have he : Finset.univ.sup S = ⨆ i, S i := by
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_true]
  rw [← he]
  exact hfin Finset.univ

/-- The physical transverse low space has at most two dimensions for each
 actual low frequency, including the exceptional zero-index fibers. -/
theorem lowTransverseSpace_finrank_le (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    Module.finrank ℂ (lowTransverseSpace N) ≤ ModeCount.spectralCountBudget N := by
  let _ := ModeCount.finite_lowFrequency N hN
  let _ : Fintype (ModeCount.LowFrequency N) := Fintype.ofFinite _
  have hreal : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hN j
  calc
    Module.finrank ℂ (lowTransverseSpace N) ≤
        ∑ ν : ModeCount.LowFrequency N,
          Module.finrank ℂ (projectedAmplitudeMap (fun j => (N j : ℝ))
            (fun j => (ν.val j : ℤ))).range := finrank_iSup_le_sum _
    _ ≤ ∑ _ν : ModeCount.LowFrequency N, 2 :=
      Finset.sum_le_sum fun ν _ => projectedAmplitudeMap_finrank_le _ hreal _
    _ = Fintype.card (Fin 2 × ModeCount.LowFrequency N) := by simp [mul_comm]
    _ ≤ ModeCount.spectralCountBudget N := ModeCount.lowFrequency_polarized_card_le N hN

#print axioms projectedAmplitudeMap_finrank_le
#print axioms lowTransverseSpace_finrank_le

end Maxwell.Continuum.BoxModes
