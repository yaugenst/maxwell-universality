import Maxwell.Continuum.CalibrationComplementMaterial

/-! Literal finite alias propagation for the calibration Neumann sum.
The result applies to its action on finite Fourier inputs while its
error theorem remains an operator-norm statement on the full fiber. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber

/-- Vanishing outside the ordinary integer alias cube. -/
def AliasSupported (u : FiberSpace) (R : ℕ) : Prop :=
  ∀ ν : Alias, (∃ j : Fin 3, (R : ℤ) < |ν j|) → u ν = 0

theorem AliasSupported.mono {u : FiberSpace} {R S : ℕ} (hu : AliasSupported u R) (hRS : R ≤ S) :
    AliasSupported u S := by
  intro ν hν
  apply hu ν
  obtain ⟨j, hj⟩ := hν
  exact ⟨j, lt_of_le_of_lt (by exact_mod_cast hRS) hj⟩

theorem AliasSupported.zero (R : ℕ) : AliasSupported (0 : FiberSpace) R := by
  intro ν _
  rfl

theorem AliasSupported.add {u v : FiberSpace} {R : ℕ}
    (hu : AliasSupported u R) (hv : AliasSupported v R) : AliasSupported (u+v) R := by
  intro ν hν
  change u ν+v ν = 0
  rw [hu ν hν, hv ν hν, add_zero]

theorem AliasSupported.smul {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) (c : ℂ) :
    AliasSupported (c • u) R := by
  intro ν hν
  change c • u ν = 0
  rw [hu ν hν, smul_zero]

theorem AliasSupported.noncentralProjection {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    AliasSupported (noncentralAliasProjection u) R := by
  intro ν hν
  rw [noncentralAliasProjection_apply, hu ν hν]
  split_ifs <;> rfl

theorem AliasSupported.freeInverse {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (t : Momentum) (e : ℂ) (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    AliasSupported ((calibrationFreeInverse t e ht he).map u) R := by
  intro ν hν
  change calibrationInverseBlock t e ν (u ν) = 0
  rw [hu ν hν, map_zero]

private theorem unitAlias_abs_le_one (j k : Fin 3) : |unitAlias j k| ≤ (1 : ℤ) := by
  classical
  by_cases hkj : k = j
  · subst k
    simp [unitAlias]
  · simp [unitAlias, hkj]

private theorem shifted_alias_outside {R : ℕ} {ν : Alias} {k : Fin 3}
    (hk : ((R+1 : ℕ) : ℤ) < |ν k|) (j : Fin 3) :
    (R : ℤ) < |(ν+unitAlias j) k| ∧ (R : ℤ) < |(ν-unitAlias j) k| := by
  have hu := unitAlias_abs_le_one j k
  have hp : |ν k| ≤ |ν k+unitAlias j k|+|unitAlias j k| := by
    have he : ν k = (ν k+unitAlias j k)-unitAlias j k := by ring
    calc
      _ = |(ν k+unitAlias j k)-unitAlias j k| := congrArg abs he
      _ ≤ _ := abs_sub _ _
  have hm : |ν k| ≤ |ν k-unitAlias j k|+|unitAlias j k| := by
    have he : ν k = (ν k-unitAlias j k)+unitAlias j k := by ring
    calc
      _ = |(ν k-unitAlias j k)+unitAlias j k| := congrArg abs he
      _ ≤ _ := abs_add_le _ _
  change (R : ℤ) < |ν k+unitAlias j k| ∧ (R : ℤ) < |ν k-unitAlias j k|
  constructor <;> omega

theorem AliasSupported.potential {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    AliasSupported (potential u) (R+1) := by
  intro ν hν
  obtain ⟨k, hk⟩ := hν
  rw [potential_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hs := shifted_alias_outside hk j
  rw [hu _ ⟨k, hs.1⟩, hu _ ⟨k, hs.2⟩, add_zero, smul_zero]

theorem AliasSupported.materialPerturbation {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    AliasSupported (calibrationMaterialPerturbation u) (R+1) := by
  exact hu.noncentralProjection.potential.noncentralProjection.smul (-(backgroundAmplitude : ℂ))

theorem AliasSupported.neumannStep {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (t : Momentum) (e : ℂ) (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    AliasSupported ((-(calibrationMaterialPerturbation*(calibrationFreeInverse t e ht he).map)) u) (R+1) := by
  have h := (hu.freeInverse t e ht he).materialPerturbation.smul (-1)
  change AliasSupported (-calibrationMaterialPerturbation ((calibrationFreeInverse t e ht he).map u)) (R+1)
  simpa only [neg_one_smul] using h

theorem AliasSupported.pow {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (T : FiberSpace →L[ℂ] FiberSpace)
    (hT : ∀ (v : FiberSpace) (S : ℕ), AliasSupported v S → AliasSupported (T v) (S+1)) (K : ℕ) :
    AliasSupported ((T^K) u) (R+K) := by
  induction K with
  | zero =>
    rw [pow_zero, Nat.add_zero]
    exact hu
  | succ K ih =>
    rw [pow_succ']
    exact hT _ _ ih

theorem AliasSupported.partialSeries {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (T : FiberSpace →L[ℂ] FiberSpace)
    (hT : ∀ (v : FiberSpace) (S : ℕ), AliasSupported v S → AliasSupported (T v) (S+1)) (K : ℕ) :
    AliasSupported (Neumann.partialSeries T K u) (R+K) := by
  intro ν hν
  change (∑ a ∈ Finset.range K, T^a) u ν = 0
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  exact ((hu.pow T hT a).mono (by have := Finset.mem_range.mp ha; omega)) ν hν

theorem calibrationInverseApprox_supported {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (t : Momentum) (e : ℂ) (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (K : ℕ) :
    AliasSupported (calibrationInverseApprox t e ht he K u) (R+K) := by
  exact (hu.partialSeries _ (fun _ _ hv => hv.neumannStep t e ht he) K).freeInverse t e ht he

theorem AliasSupported.finite_support {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    (Function.support (u : Alias → Polarization)).Finite := by
  have hf : Set.Finite {ν : Alias | ∀ j, ν j ∈ Set.Icc (-(R : ℤ)) (R : ℤ)} :=
    Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Icc _ _)
  apply hf.subset
  intro ν hν j
  have ha : |ν j| ≤ (R : ℤ) := by
    by_contra hn
    exact hν (hu ν ⟨j, lt_of_not_ge hn⟩)
  exact abs_le.mp ha

#print axioms calibrationInverseApprox_supported
#print axioms AliasSupported.finite_support

end Maxwell.Continuum.Calibration
