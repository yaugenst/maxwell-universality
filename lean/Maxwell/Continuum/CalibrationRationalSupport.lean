import Maxwell.Continuum.CalibrationRationalNeumann

/-! Exact finite propagation of the executable rational stencil, for
real or complex coefficient modules. This controls the materialized
array boundary without an additional truncation-error assumption. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def RationalSupported (f : Alias → Fin 3 → V) (R : ℕ) : Prop :=
  ∀ ν, (∃ j, (R : ℤ) < |ν j|) → ∀ i, f ν i = 0

omit [Module ℚ V] in
theorem RationalSupported.zero (R : ℕ) : RationalSupported (0 : Alias → Fin 3 → V) R := by
  intro ν hν i
  rfl

omit [Module ℚ V] in
theorem RationalSupported.mono {f : Alias → Fin 3 → V} {R S : ℕ}
    (hf : RationalSupported f R) (hRS : R ≤ S) : RationalSupported f S := by
  intro ν hν i
  obtain ⟨j,hj⟩ := hν
  exact hf ν ⟨j,lt_of_le_of_lt (by exact_mod_cast hRS) hj⟩ i

omit [Module ℚ V] in
theorem RationalSupported.sub {f g : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (hg : RationalSupported g R) : RationalSupported (f-g) R := by
  intro ν hν i
  change f ν i-g ν i = 0
  rw [hf ν hν i,hg ν hν i,sub_self]

theorem RationalSupported.smul {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (c : ℚ) : RationalSupported (c • f) R := by
  intro ν hν i
  change c • f ν i = 0
  rw [hf ν hν i,smul_zero]

omit [Module ℚ V] in
theorem RationalSupported.noncentral {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalNoncentral f) R := by
  intro ν hν i
  unfold rationalNoncentral
  split_ifs
  · rfl
  · exact hf ν hν i

private theorem rational_shifted_outside {R : ℕ} {ν : Alias} {k : Fin 3}
    (hk : ((R+1 : ℕ) : ℤ) < |ν k|) (j : Fin 3) :
    (R : ℤ) < |(ν+unitAlias j) k| ∧ (R : ℤ) < |(ν-unitAlias j) k| := by
  have hu : |unitAlias j k| ≤ (1 : ℤ) := by
    classical
    by_cases hkj : k = j <;> simp [unitAlias,hkj]
  have hp : |ν k| ≤ |ν k+unitAlias j k|+|unitAlias j k| := by
    have h := abs_sub (ν k+unitAlias j k) (unitAlias j k)
    simpa only [add_sub_cancel_right] using h
  have hm : |ν k| ≤ |ν k-unitAlias j k|+|unitAlias j k| := by
    have h := abs_add_le (ν k-unitAlias j k) (unitAlias j k)
    simpa only [sub_add_cancel] using h
  change (R : ℤ) < |ν k+unitAlias j k| ∧ (R : ℤ) < |ν k-unitAlias j k|
  constructor <;> omega

theorem RationalSupported.potential {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalPotential f) (R+1) := by
  intro ν hν i
  obtain ⟨k,hk⟩ := hν
  unfold rationalPotential
  apply Finset.sum_eq_zero
  intro j _
  have hs := rational_shifted_outside hk j
  rw [hf _ ⟨k,hs.1⟩ i,hf _ ⟨k,hs.2⟩ i,add_zero,smul_zero]

theorem RationalSupported.perturbation {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalPerturbation f) (R+1) :=
  hf.noncentral.potential.noncentral.smul _

theorem RationalSupported.freeApply {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (t E : ℚ) (r : Fin 3 → ℚ) :
    RationalSupported (rationalFreeApply t E r f) R := by
  intro ν hν i
  unfold rationalFreeApply
  apply Finset.sum_eq_zero
  intro j _
  rw [hf ν hν j,smul_zero]

theorem RationalSupported.inverseApply {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) :
    RationalSupported (rationalInverseApply t E r f K) (R+K) := by
  induction K with
  | zero => exact RationalSupported.zero _
  | succ K ih =>
    exact ((hf.freeApply t E r).mono (by omega)).sub
      (by simpa only [Nat.add_assoc] using ih.perturbation.freeApply t E r)

#print axioms RationalSupported.inverseApply

end Maxwell.Continuum.Calibration
