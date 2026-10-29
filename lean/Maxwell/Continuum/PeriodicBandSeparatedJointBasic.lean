import Maxwell.Continuum.PeriodicBandSeparatedIdentity

/-! A bounded reference-resolvent formula for the separated inverse. The
reference energy is fixed away from every constructed band. All inverse
laws at the band follow from proved separated-resolvent identities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic Metric Set

attribute [local irreducible] fullSeparatedResolvent fullResolventExtension
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot scaledBand

def referenceEnergy : ℂ := (Corner.lambdaStar : ℂ) + 1 / 100

theorem referenceEnergy_distance : ‖referenceEnergy - (Corner.lambdaStar : ℂ)‖ = 1 / 100 := by
  simp only [referenceEnergy, add_sub_cancel_left]
  norm_num

theorem referenceEnergy_mem : referenceEnergy ∈ energyDisk := by
  change referenceEnergy ∈ closedBall (Corner.lambdaStar : ℂ) (1 / 100)
  rw [mem_closedBall, dist_eq_norm, referenceEnergy_distance]

theorem referenceEnergy_ne_band {t : Momentum} (ht : t ∈ chart) : referenceEnergy ≠ scaledBand t := by
  intro heq
  have h := scaledBand_center_bound ht
  rw [← heq, referenceEnergy_distance] at h
  norm_num at h

def referenceSeparated (t : Momentum) : FiberMap :=
  fullResolventExtension (t, referenceEnergy) * fullBandComplement t

theorem referenceSeparated_eq {t : Momentum} (ht : t ∈ chart) :
    referenceSeparated t = fullSeparatedResolvent t referenceEnergy :=
  (fullSeparated_eq_resolvent_complement ht referenceEnergy_mem (referenceEnergy_ne_band ht)).symm

def separatedDenominator (z : Parameter) : FiberMap :=
  1 - ((backgroundAmplitude : ℂ) * (z.2 - referenceEnergy)) • referenceSeparated z.1

def separatedDenominatorInverse (z : Parameter) : FiberMap :=
  1 + ((backgroundAmplitude : ℂ) * (z.2 - referenceEnergy)) • fullSeparatedResolvent z.1 z.2

theorem separated_inverse_algebra_right (d : ℂ) (A S : FiberMap) :
    (1 - d • A) * (1 + d • S) = 1 + d • (S - A - d • (A * S)) := by
  simp only [mul_add, sub_mul, mul_one, one_mul, fiberMap_smul_mul, fiberMap_mul_smul,
    smul_sub, smul_smul]
  module

theorem separated_inverse_algebra_left (d : ℂ) (A S : FiberMap) :
    (1 + d • S) * (1 - d • A) = 1 + d • (S - A - d • (S * A)) := by
  simp only [mul_sub, add_mul, mul_one, one_mul, fiberMap_smul_mul, fiberMap_mul_smul,
    smul_sub, smul_smul]
  module

theorem separatedDenominator_inverse_right {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) :
    separatedDenominator (t, e) * separatedDenominatorInverse (t, e) = 1 := by
  have h := fullSeparated_identity_rev ht he referenceEnergy_mem (referenceEnergy_ne_band ht)
  rw [← referenceSeparated_eq ht] at h
  let d : ℂ := (backgroundAmplitude : ℂ) * (e - referenceEnergy)
  change fullSeparatedResolvent t e - referenceSeparated t =
    d • (referenceSeparated t * fullSeparatedResolvent t e) at h
  dsimp only [separatedDenominator, separatedDenominatorInverse]
  calc
    _ = 1 + d • (fullSeparatedResolvent t e - referenceSeparated t -
        d • (referenceSeparated t * fullSeparatedResolvent t e)) :=
      separated_inverse_algebra_right d _ _
    _ = 1 := by rw [h, sub_self, smul_zero, add_zero]

theorem separatedDenominator_inverse_left {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) :
    separatedDenominatorInverse (t, e) * separatedDenominator (t, e) = 1 := by
  have h := fullSeparated_identity ht he referenceEnergy_mem (referenceEnergy_ne_band ht)
  rw [← referenceSeparated_eq ht] at h
  let d : ℂ := (backgroundAmplitude : ℂ) * (e - referenceEnergy)
  change fullSeparatedResolvent t e - referenceSeparated t =
    d • (fullSeparatedResolvent t e * referenceSeparated t) at h
  dsimp only [separatedDenominator, separatedDenominatorInverse]
  calc
    _ = 1 + d • (fullSeparatedResolvent t e - referenceSeparated t -
        d • (fullSeparatedResolvent t e * referenceSeparated t)) :=
      separated_inverse_algebra_left d _ _
    _ = 1 := by rw [h, sub_self, smul_zero, add_zero]

theorem separatedDenominator_isUnit {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) : IsUnit (separatedDenominator (t, e)) :=
  ⟨⟨separatedDenominator (t, e), separatedDenominatorInverse (t, e),
    separatedDenominator_inverse_right ht he, separatedDenominator_inverse_left ht he⟩, rfl⟩

def jointSeparatedResolvent (z : Parameter) : FiberMap :=
  referenceSeparated z.1 * Ring.inverse (separatedDenominator z)

theorem jointSeparatedResolvent_eq {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) : jointSeparatedResolvent (t, e) = fullSeparatedResolvent t e := by
  have h := fullSeparated_identity ht he referenceEnergy_mem (referenceEnergy_ne_band ht)
  rw [← referenceSeparated_eq ht] at h
  have hmul : fullSeparatedResolvent t e * separatedDenominator (t, e) = referenceSeparated t := by
    rw [separatedDenominator, mul_sub, mul_one, fiberMap_mul_smul, ← h]
    abel
  have hi := congrArg (fun A : FiberMap => A * Ring.inverse (separatedDenominator (t, e))) hmul
  rw [mul_assoc, Ring.mul_inverse_cancel _ (separatedDenominator_isUnit ht he), mul_one] at hi
  exact hi.symm

end Maxwell.Continuum.PeriodicBand
