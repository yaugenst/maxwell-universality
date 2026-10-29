import Maxwell.Continuum.BoxModesLowSpace

/-! The finite physical low-frequency space is in the operator domain and invariant. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped InnerProductSpace BigOperators

theorem box_transverseProjection_coe (N : Fin 3 → ℝ)
    (u : transverseSpace (boxDomain N)) :
    transverseProjection (boxDomain N) (u : testL2Closure (boxDomain N)) = u :=
  (transverseSpace (boxDomain N)).orthogonalProjectionOnto_mem_subspace_eq_self u

theorem projectedComponent_eigen (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    transverseCurlCurl (boxDomain N)
        (domainTransverseProjection (boxDomain N) (operatorComponentMode N hN ν c)) =
      (modeEigenvalue N ν : ℂ) •
        (domainTransverseProjection (boxDomain N) (operatorComponentMode N hN ν c) :
          transverseSpace (boxDomain N)) := by
  have hp := congrArg (transverseProjection (boxDomain N))
    (transverseCurlCurl_projection (boxDomain N) (operatorComponentMode N hN ν c))
  have hlong : transverseProjection (boxDomain N) (longitudinalMode N ν) = 0 :=
    projectedAmplitudeMap_momentum_zero N hN ν
  rw [box_transverseProjection_coe N _] at hp
  rw [componentMode_operator_decompose N hN ν c] at hp
  let P := transverseProjection (boxDomain N)
  have hs : P ((modeEigenvalue N ν : ℂ) • componentMode N c ν -
      (integerWaveNumber N ν c : ℂ) • longitudinalMode N ν) =
      (modeEigenvalue N ν : ℂ) • P (componentMode N c ν) -
        (integerWaveNumber N ν c : ℂ) • P (longitudinalMode N ν) :=
    (P.map_sub _ _).trans (congrArg₂ (fun x y => x - y)
      (P.map_smul (modeEigenvalue N ν : ℂ) (componentMode N c ν))
      (P.map_smul (integerWaveNumber N ν c : ℂ) (longitudinalMode N ν)))
  have hP : P (longitudinalMode N ν) = 0 := hlong
  rw [hP, smul_zero, sub_zero] at hs
  exact hp.trans hs

def projectedOperatorAmplitude (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) : (transverseCurlCurl (boxDomain N)).domain :=
  ∑ c : Fin 3, a c •
    domainTransverseProjection (boxDomain N) (operatorComponentMode N hN ν c)

theorem projectedOperatorAmplitude_coe (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    (projectedOperatorAmplitude N hN ν a : transverseSpace (boxDomain N)) =
      projectedAmplitudeMap N ν a := by
  change (∑ c : Fin 3, a c • transverseProjection (boxDomain N) (componentMode N c ν)) =
    transverseProjection (boxDomain N) (boxAmplitude N ν a)
  rw [boxAmplitude_eq_sum, map_sum]
  simp only [map_smul]

theorem projectedOperatorAmplitude_eigen (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    transverseCurlCurl (boxDomain N) (projectedOperatorAmplitude N hN ν a) =
      (modeEigenvalue N ν : ℂ) • projectedAmplitudeMap N ν a := by
  change (transverseCurlCurl (boxDomain N)).toFun
    (∑ c : Fin 3, a c •
      domainTransverseProjection (boxDomain N) (operatorComponentMode N hN ν c)) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ c : Fin 3, a c • transverseCurlCurl (boxDomain N)
    (domainTransverseProjection (boxDomain N) (operatorComponentMode N hN ν c))) = _
  simp_rw [projectedComponent_eigen N hN ν]
  rw [← projectedOperatorAmplitude_coe N hN ν a]
  change (∑ c : Fin 3, a c • ((modeEigenvalue N ν : ℂ) •
      transverseProjection (boxDomain N) (componentMode N c ν))) =
    (modeEigenvalue N ν : ℂ) •
      ∑ c : Fin 3, a c • transverseProjection (boxDomain N) (componentMode N c ν)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _

theorem projectedAmplitudeMap_mem_domain (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    projectedAmplitudeMap N ν a ∈ (transverseCurlCurl (boxDomain N)).domain := by
  rw [← projectedOperatorAmplitude_coe N hN ν a]
  exact (projectedOperatorAmplitude N hN ν a).property

theorem projectedAmplitudeMap_operator (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ)
    (hu : projectedAmplitudeMap N ν a ∈ (transverseCurlCurl (boxDomain N)).domain) :
    transverseCurlCurl (boxDomain N) ⟨projectedAmplitudeMap N ν a, hu⟩ =
      (modeEigenvalue N ν : ℂ) • projectedAmplitudeMap N ν a := by
  have he : (⟨projectedAmplitudeMap N ν a, hu⟩ : (transverseCurlCurl (boxDomain N)).domain) =
      projectedOperatorAmplitude N hN ν a :=
    Subtype.ext (projectedOperatorAmplitude_coe N hN ν a).symm
  rw [he]
  exact projectedOperatorAmplitude_eigen N hN ν a

theorem lowTransverseSpace_subset_domain (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    lowTransverseSpace N ≤
      (transverseCurlCurl (boxDomain (fun j => (N j : ℝ)))).domain := by
  apply iSup_le
  intro ν x hx
  obtain ⟨a, rfl⟩ := hx
  exact projectedAmplitudeMap_mem_domain _ (fun j => by exact_mod_cast hN j) _ a

/-- Every low vector belongs to the full transverse operator domain and
its image stays in the same finite physical low space. -/
theorem lowTransverseSpace_invariant (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    InvariantRestriction.Data
      (transverseCurlCurl (boxDomain (fun j => (N j : ℝ)))) (lowTransverseSpace N) where
  subset_domain := lowTransverseSpace_subset_domain N hN
  map_mem := by
    let A := transverseCurlCurl (boxDomain (fun j => (N j : ℝ)))
    let K := lowTransverseSpace N
    let P : Submodule ℂ (transverseSpace (boxDomain (fun j => (N j : ℝ)))) :=
      (K.comap A.toFun).map A.domain.subtype
    have hle : K ≤ P := by
      apply iSup_le
      intro ν x hx
      obtain ⟨a, rfl⟩ := hx
      refine ⟨⟨_, projectedAmplitudeMap_mem_domain _ (fun j => by exact_mod_cast hN j) _ a⟩,
        ?_, rfl⟩
      change A ⟨_, _⟩ ∈ K
      rw [projectedAmplitudeMap_operator _ (fun j => by exact_mod_cast hN j)]
      apply K.smul_mem
      exact Submodule.mem_iSup_of_mem ν ⟨a, rfl⟩
    intro x
    obtain ⟨d, hd, hx⟩ := hle x.property
    have he : d = ⟨(x : transverseSpace (boxDomain (fun j => (N j : ℝ)))),
        lowTransverseSpace_subset_domain N hN x.property⟩ := Subtype.ext hx
    change A d ∈ K at hd
    rw [he] at hd
    exact hd

#print axioms lowTransverseSpace_invariant

end Maxwell.Continuum.BoxModes
