import Maxwell.Continuum.BlochPeriodicPotential

/-! Equality between the literal physical dielectric multiplier and its Bloch fiber action. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

theorem physicalPotential_apply (u : FieldL2) (i : Fin 3) :
    physicalPotential u i = ∑ j : Fin 3, (FreeFiber.potentialWeight j : ℂ) •
      (modulation (aliasFrequency (FreeFiber.unitAlias j)) (u i) +
        modulation (aliasFrequency (-FreeFiber.unitAlias j)) (u i)) := by
  simp only [physicalPotential, sum_apply, smul_apply, add_apply]
  change (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) i : FieldL2 →L[ℂ] ScalarL2)
    (∑ j : Fin 3, (FreeFiber.potentialWeight j : ℂ) •
      (fieldModulation (aliasFrequency (FreeFiber.unitAlias j)) u +
        fieldModulation (aliasFrequency (-FreeFiber.unitAlias j)) u)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem weightedPhasePair_ae (j : Fin 3) (f : ScalarL2) :
    ((FreeFiber.potentialWeight j : ℂ) •
      (modulation (aliasFrequency (FreeFiber.unitAlias j)) f +
        modulation (aliasFrequency (-FreeFiber.unitAlias j)) f) : ScalarL2) =ᵐ[volume]
      (fun x => ((2 * FreeFiber.potentialWeight j) * Real.cos (Real.pi * x j) : ℝ) * f x) := by
  have hs := Lp.coeFn_smul (FreeFiber.potentialWeight j : ℂ)
    (modulation (aliasFrequency (FreeFiber.unitAlias j)) f +
      modulation (aliasFrequency (-FreeFiber.unitAlias j)) f)
  filter_upwards [hs,
    Lp.coeFn_add (modulation (aliasFrequency (FreeFiber.unitAlias j)) f)
      (modulation (aliasFrequency (-FreeFiber.unitAlias j)) f),
    modulation_ae (aliasFrequency (FreeFiber.unitAlias j)) f,
    modulation_ae (aliasFrequency (-FreeFiber.unitAlias j)) f] with x hs ha hp hn
  rw [hs]
  change (FreeFiber.potentialWeight j : ℂ) *
    (modulation (aliasFrequency (FreeFiber.unitAlias j)) f +
      modulation (aliasFrequency (-FreeFiber.unitAlias j)) f) x = _
  rw [ha]
  simp only [Pi.add_apply, hp, hn]
  rw [← add_mul, phase_pair_cosine]
  push_cast
  ring

theorem physicalPotential_ae (u : FieldL2) (i : Fin 3) :
    physicalPotential u i =ᵐ[volume]
      (fun x => (PeriodicMaterial.periodicPotential x : ℂ) * u i x) := by
  rw [physicalPotential_apply]
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin 3 =>
    (FreeFiber.potentialWeight j : ℂ) •
      (modulation (aliasFrequency (FreeFiber.unitAlias j)) (u i) +
        modulation (aliasFrequency (-FreeFiber.unitAlias j)) (u i)))
  have hp := ae_all_iff.mpr (fun j : Fin 3 => weightedPhasePair_ae j (u i))
  filter_upwards [hs, hp] with x hs hp
  rw [hs, PeriodicMaterial.periodicPotential_sum]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos] using hp j

/-- The prescribed 6–8 scalar dielectric is precisely 7I plus the physical potential. -/
theorem periodicMultiplier_eq (u : FieldL2) :
    PeriodicMaterial.dielectric.multiplier u = (7 : ℂ) • u +
      (FreeFiber.backgroundAmplitude : ℂ) • physicalPotential u := by
  apply PiLp.ext
  intro i
  change PeriodicMaterial.dielectric.multiplier u i =
    (7 : ℂ) • u i + (FreeFiber.backgroundAmplitude : ℂ) • physicalPotential u i
  apply Lp.ext
  filter_upwards [PeriodicMaterial.dielectric.multiplier_ae u i,
    physicalPotential_ae u i,
    Lp.coeFn_add ((7 : ℂ) • u i)
      ((FreeFiber.backgroundAmplitude : ℂ) • physicalPotential u i),
    Lp.coeFn_smul (7 : ℂ) (u i),
    Lp.coeFn_smul (FreeFiber.backgroundAmplitude : ℂ) (physicalPotential u i)]
      with x hm hp ha h7 hρ
  rw [hm, ha]
  simp only [Pi.add_apply, h7, hρ, Pi.smul_apply, smul_eq_mul, hp]
  change ((7 + FreeFiber.backgroundAmplitude * PeriodicMaterial.periodicPotential x : ℝ) : ℂ) *
    u i x = _
  push_cast
  ring

/-- The actual scalar dielectric multiplication is intertwined with the proven
infinite six-neighbor fiber coupling. -/
theorem unitary_periodicMultiplier (u : FieldL2) :
    unitary (PeriodicMaterial.dielectric.multiplier u) = (7 : ℂ) • unitary u +
      (FreeFiber.backgroundAmplitude : ℂ) • potentialL2 (unitary u) := by
  rw [periodicMultiplier_eq, map_add, map_smul, map_smul, unitary_physicalPotential]

end Maxwell.Continuum.Bloch
