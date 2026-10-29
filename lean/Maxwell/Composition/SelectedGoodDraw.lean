import Maxwell.Composition.SelectedProbability
import Maxwell.Main

/-! Bind the selected physical construction to the literal all-output event
and cardinal success probability in the main realization statement. -/
noncomputable section
namespace Maxwell.Realization

theorem successProbability_of_bad (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) (bits : ℕ) (emitted : Draw bits → Target.Instance S.n)
    (bad : Finset ℕ) (hbad : bad ⊆ Finset.range (2^bits)) (failure : ℝ)
    (hfailure : Probability.gridProbability (2^bits) (pow_pos (by norm_num) _) bad ≤ failure)
    (hgood : ∀ j : Draw bits, j.val ∉ bad → GoodDraw p C S (emitted j)) :
    1-failure ≤ successProbability p C S emitted := by
  classical
  let g := goodDraws p C S emitted
  have hJ : (0 : ℝ) < ((2^bits : ℕ) : ℝ) := by positivity
  have hsub : Finset.range (2^bits) ⊆ g.image Fin.val ∪ bad := by
    intro k hk
    have hkJ : k < 2^bits := Finset.mem_range.mp hk
    by_cases hb : k ∈ bad
    · exact Finset.mem_union_right _ hb
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨⟨k,hkJ⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood ⟨k,hkJ⟩ hb⟩, rfl⟩
  have hcard : 2^bits ≤ g.card+bad.card := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa only [Finset.card_range, Finset.card_image_of_injective _ Fin.val_injective] using h
  have hcardR : ((2:ℕ)^bits : ℝ) ≤ g.card+bad.card := by exact_mod_cast hcard
  rw [Probability.gridProbability_eq _ _ _ hbad] at hfailure
  have hbR := (div_le_iff₀ hJ).mp hfailure
  change 1-failure ≤ (g.card : ℝ)/(2:ℝ)^bits
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hJ hcardR hbR
  apply (le_div_iff₀ hJ).mpr
  nlinarith

end Maxwell.Realization

namespace Maxwell.Composition.SelectedInstance.Input
open Maxwell.Realization
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

variable (I : Input) (R : SelectedPlatform)

theorem goodDraw (p : Source.Parameters) (C : Constants)
    (J : ℕ) (j : Fin J) (hj : j.val ∉ I.bad R J)
    (hunit : IsUnit (Source.realMatrix I.source)) (hm : 2 ≤ I.source.nnz)
    (hb : I.source.source ≠ 0) (hp : 1 ≤ I.precision) (haccuracy : I.accuracy ≤ 1)
    (hcondition : (I.source.nnz : ℝ)*condition₂ (Source.realMatrix I.source) ≤ I.sourceBound)
    (hprecision : (I.source.nnz : ℝ)/(2*2^I.precision) ≤ (I.accuracy : ℝ)/(64*I.sourceBound))
    (hconditionPower : 16*(I.fullBudget R : ℝ) ≤
      (max 1 I.source.nnz : ℝ)^(C.conditionPower : ℝ))
    (haccuracyFloor : (I.accuracy : ℝ) ≤ (I.source.nnz : ℝ)^(-p.accuracyExponent)) :
    GoodDraw p C I.source (I.target R J j) := by
  obtain ⟨hu,hc,hy⟩ := I.sound R J j hj hunit hm hb hp haccuracy hcondition hprecision
  refine ⟨hu,hc.trans hconditionPower,?_⟩
  intro y hy'
  obtain ⟨hf,he,hw⟩ := hy y hy'
  refine ⟨hf,he,?_⟩
  intro w hw' eta heta
  exact hw w hw' eta (haccuracyFloor.trans heta.1)

theorem bad_subset (J : ℕ) : I.bad R J ⊆ Finset.range J :=
  Probability.spectralBad_subset (PhysicalBackground.eigenvalues R.physical (I.box R))
    (PhysicalGram.width R.physical (I.zeta R) (I.zeta_pos R))
    (Probability.detuningRadius I.source.nnz (Fintype.card (I.box R).Edge)
      (PhysicalGram.width R.physical (I.zeta R) (I.zeta_pos R))) J

/-- The common spectral event is contained in the main all-output event.
The only remaining global numerical obligations are the fixed condition
exponent and the chosen lower accuracy floor. -/
theorem success_probability (p : Source.Parameters) (C : Constants)
    (hunit : IsUnit (Source.realMatrix I.source)) (hm : 2 ≤ I.source.nnz)
    (hb : I.source.source ≠ 0) (hp : 1 ≤ I.precision) (haccuracy : I.accuracy ≤ 1)
    (hcondition : (I.source.nnz : ℝ)*condition₂ (Source.realMatrix I.source) ≤ I.sourceBound)
    (hprecision : (I.source.nnz : ℝ)/(2*2^I.precision) ≤ (I.accuracy : ℝ)/(64*I.sourceBound))
    (hconditionPower : 16*(I.fullBudget R : ℝ) ≤
      (max 1 I.source.nnz : ℝ)^(C.conditionPower : ℝ))
    (haccuracyFloor : (I.accuracy : ℝ) ≤ (I.source.nnz : ℝ)^(-p.accuracyExponent)) :
    1-3/(64*(I.source.nnz : ℝ)) ≤
      successProbability p C I.source (randomBits := I.randomBits R)
        (I.target R (2^I.randomBits R)) := by
  apply successProbability_of_bad p C I.source (I.randomBits R)
    (I.target R (2^I.randomBits R)) (I.bad R (2^I.randomBits R))
    (I.bad_subset R _) _ (I.random_failure_probability R)
  intro j hj
  exact I.goodDraw R p C _ j hj hunit hm hb hp haccuracy hcondition hprecision
    hconditionPower haccuracyFloor

end Maxwell.Composition.SelectedInstance.Input
