import Maxwell.Continuum.BoxModesLowInvariant
import Maxwell.Continuum.HilbertCoefficientEnergy

/-!
# High-mode energy for the actual PEC-box operator

The concrete finite low subspace has the stated dimension bound, is invariant
in the represented operator domain, and leaves free energy at least26 on its
orthogonal complement. This binds the integer mode count to the continuum
PEC operator rather than to an abstract Fourier model.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped InnerProductSpace BigOperators

theorem admissibleIndex_nonneg (c : Fin 3) (ν : Fin 3 → ℤ)
    (hν : AdmissibleIndex c ν) (j : Fin 3) : 0 ≤ ν j := by
  by_cases hj : j = c
  · subst j
    exact hν.1
  · exact (hν.2 j hj).le

theorem modeEigenvalue_eq_free (N : ModeCount.BoxLengths) (ν : Fin 3 → ℤ)
    (hν : ∀ j, 0 ≤ ν j) :
    modeEigenvalue (fun j => (N j : ℝ)) ν =
      ModeCount.freeEigenvalue N (fun j => (ν j).toNat) := by
  apply Finset.sum_congr rfl
  intro j _
  have hcast : (((ν j).toNat : ℕ) : ℝ) = (ν j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hν j)
  change ((ν j : ℝ) * Real.pi / (N j : ℝ)) ^ 2 =
    (Real.pi * ((ν j).toNat : ℝ) / (N j : ℝ)) ^ 2
  rw [hcast, mul_comm (ν j : ℝ) Real.pi]

theorem low_component_projection_mem (N : ModeCount.BoxLengths) (q : ComponentModeIndex)
    (hq : modeEigenvalue (fun j => (N j : ℝ)) q.2.val ≤ 26) :
    transverseProjection (boxDomain (fun j => (N j : ℝ)))
      (indexedComponentMode (fun j => (N j : ℝ)) q) ∈ lowTransverseSpace N := by
  let ν : ModeCount.LowFrequency N :=
    ⟨fun j => (q.2.val j).toNat,
      by rw [← modeEigenvalue_eq_free N q.2.val (admissibleIndex_nonneg _ _ q.2.property)]; exact hq⟩
  have hν : (fun j => (ν.val j : ℤ)) = q.2.val := by
    funext j
    exact Int.toNat_of_nonneg (admissibleIndex_nonneg _ _ q.2.property j)
  apply Submodule.mem_iSup_of_mem ν
  refine ⟨Pi.single q.1 1, ?_⟩
  change transverseProjection _ (boxAmplitude _ (fun j => (ν.val j : ℤ)) _) = _
  rw [hν, boxAmplitude_single]
  rfl

theorem low_coefficient_eq_zero (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)
    (u : transverseSpace (boxDomain (fun j => (N j : ℝ))))
    (hu : u ∈ (lowTransverseSpace N)ᗮ) (q : ComponentModeIndex)
    (hq : modeEigenvalue (fun j => (N j : ℝ)) q.2.val ≤ 26) :
    (componentHilbertBasis (fun j => (N j : ℝ)) (fun j => by exact_mod_cast hN j)).repr
      (u : testL2Closure (boxDomain (fun j => (N j : ℝ)))) q = 0 := by
  have hp := hu _ (low_component_projection_mem N q hq)
  change inner ℂ ((transverseSpace (boxDomain (fun j => (N j : ℝ)))).orthogonalProjectionOnto
    (indexedComponentMode (fun j => (N j : ℝ)) q)) u = 0 at hp
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at hp
  rw [HilbertBasis.repr_apply_apply, componentHilbertBasis_apply,
    normalizedComponentMode, inner_smul_left, hp, mul_zero]

/-- High-frequency coercivity for the actual self-adjoint transverse
curl-curl operator on the literal physical box. -/
theorem lowTransverseSpace_high (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)
    (u : (transverseCurlCurl (boxDomain (fun j => (N j : ℝ)))).domain)
    (hu : (u : transverseSpace (boxDomain (fun j => (N j : ℝ)))) ∈ (lowTransverseSpace N)ᗮ) :
    26 * ‖(u : transverseSpace (boxDomain (fun j => (N j : ℝ))))‖ ^ 2 ≤
      (inner ℂ (u : transverseSpace (boxDomain (fun j => (N j : ℝ))))
        (transverseCurlCurl (boxDomain (fun j => (N j : ℝ))) u)).re := by
  let R : Fin 3 → ℝ := fun j => (N j : ℝ)
  let Ω := boxDomain R
  let hreal : ∀ j, 0 < R j := fun j => by
    change (0 : ℝ) < N j
    exact_mod_cast hN j
  let x : testL2Closure Ω := (u : transverseSpace Ω)
  let y : testL2Closure Ω := transverseCurlCurl Ω u
  have hcoeff : ∀ q : ComponentModeIndex,
      (componentHilbertBasis R hreal).repr y q =
        (modeEigenvalue R q.2.val : ℂ) • (componentHilbertBasis R hreal).repr x q :=
    transverseCurlCurl_coefficient R hreal u
  have hhigh : ∀ q : ComponentModeIndex, (componentHilbertBasis R hreal).repr x q ≠ 0 →
      26 ≤ modeEigenvalue R q.2.val := by
    intro q hq
    by_contra hnot
    exact hq (low_coefficient_eq_zero N hN (u : transverseSpace Ω) hu q
      (le_of_lt (lt_of_not_ge hnot)))
  have he := HilbertCoefficientEnergy.energy_lower
    (componentHilbertBasis R hreal) x y (fun q => modeEigenvalue R q.2.val) 26 hcoeff hhigh
  exact he


#print axioms lowTransverseSpace_high

end Maxwell.Continuum.BoxModes
