import Maxwell.Continuum.CalibrationCoefficientEntries

/-! Each scalar matrix entry uses one free-block entry and a six-neighbor
weight. This eliminates the redundant polarization sum from table emission. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber
set_option maxHeartbeats 2500000

def neighborWeight (ν μ : Alias) : ℚ := ∑ d : Fin 3, rationalWeight d *
  ((if ν+unitAlias d=μ then 1 else 0)+(if ν-unitAlias d=μ then 1 else 0))

theorem noncentral_pointBasis (μ ν : Alias) (j k : Fin 3) :
    rationalNoncentral (pointBasis μ j) ν k=
      if rationalCentralCheck μ then 0 else (if ν=μ then 1 else 0)*(if k=j then 1 else 0) := by
  by_cases hν : ν=μ
  · subst ν
    simp [rationalNoncentral,pointBasis]
  · simp [rationalNoncentral,pointBasis,hν]

theorem potential_pointBasis (μ ν : Alias) (j k : Fin 3) :
    rationalPotential (rationalNoncentral (pointBasis μ j)) ν k=
      if rationalCentralCheck μ then 0 else neighborWeight ν μ*(if k=j then 1 else 0) := by
  unfold rationalPotential
  simp_rw [noncentral_pointBasis]
  by_cases hμ : rationalCentralCheck μ=true
  · simp [hμ]
  · by_cases hk : k=j <;> simp [hμ,hk,neighborWeight,smul_eq_mul]

theorem perturbation_pointBasis (μ ν : Alias) (j k : Fin 3) :
    rationalPerturbation (pointBasis μ j) ν k=
      if rationalCentralCheck ν || rationalCentralCheck μ then 0
      else -rationalAmplitude*neighborWeight ν μ*(if k=j then 1 else 0) := by
  change -rationalAmplitude*(if rationalCentralCheck ν then 0 else
    rationalPotential (rationalNoncentral (pointBasis μ j)) ν k)=_
  rw [potential_pointBasis]
  by_cases hν : rationalCentralCheck ν=true <;>
    by_cases hμ : rationalCentralCheck μ=true <;> simp [hν,hμ]

theorem stencilEntry_factor (t E : ℚ) (r : Fin 3 → ℚ) (ν : Alias) (i : Fin 3)
    (μ : Alias) (j : Fin 3) :
    stencilEntry t E r ν i μ j=
      if rationalCentralCheck ν || rationalCentralCheck μ then 0
      else rationalAmplitude*rationalFreeInverseMatrix t E r ν i j*neighborWeight ν μ := by
  change -(∑ k : Fin 3, rationalFreeInverseMatrix t E r ν i k*
    rationalPerturbation (pointBasis μ j) ν k)=_
  simp_rw [perturbation_pointBasis]
  split_ifs with h
  · simp
  · have he (k : Fin 3) : rationalFreeInverseMatrix t E r ν i k*
        (-rationalAmplitude*neighborWeight ν μ*(if k=j then 1 else 0))=
        if k=j then -rationalAmplitude*rationalFreeInverseMatrix t E r ν i j*neighborWeight ν μ else 0 := by
      by_cases hk : k=j
      · subst k; simp only [ite_true,mul_one]; ring
      · simp [hk]
    simp_rw [he]
    simp

#print axioms stencilEntry_factor

end Maxwell.Continuum.Calibration
