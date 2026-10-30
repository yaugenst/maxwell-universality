import Maxwell.Continuum.CalibrationSupercellEmbedding
import Maxwell.Continuum.CalibrationFiniteApplication
import Maxwell.Continuum.CalibrationFiniteNormalizeData

/-! Exact physical interpretation of the finite-array iteration. The
embedding is the actual normalized supercell Fourier construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber NormedSpace

variable (M : ℕ) [NeZero M]

def physicalLift (T : FiberSpace →L[ℂ] FiberSpace) : FieldL2 →L[ℂ] FieldL2 :=
  (embedding M).toContinuousLinearMap.comp
    (T.comp (embedding M).toContinuousLinearMap.adjoint)

theorem physicalLift_apply (T : FiberSpace →L[ℂ] FiberSpace) (u : FiberSpace) :
    physicalLift M T (embedding M u)=embedding M (T u) := by
  have he : (embedding M).toContinuousLinearMap.adjoint (embedding M u)=u :=
    congrArg (fun S : FiberSpace →L[ℂ] FiberSpace => S u) (embedding M).adjoint_comp_self
  change embedding M (T ((embedding M).toContinuousLinearMap.adjoint (embedding M u)))=_
  rw [he]

theorem physicalLift_norm (T : FiberSpace →L[ℂ] FiberSpace) : ‖physicalLift M T‖ ≤ ‖T‖ := by
  rw [physicalLift,LinearIsometry.norm_toContinuousLinearMap_comp]
  have hJ : ‖(embedding M).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (embedding M).norm_toContinuousLinearMap_le
  exact (T.opNorm_comp_le _).trans
    ((mul_le_mul_of_nonneg_left hJ (norm_nonneg T)).trans_eq (mul_one _))

theorem physicalLift_sub (T S : FiberSpace →L[ℂ] FiberSpace) :
    physicalLift M T-physicalLift M S=physicalLift M (T-S) := by
  apply ContinuousLinearMap.ext
  intro u
  change embedding M (T _)-embedding M (S _)=embedding M ((T-S) _)
  rw [← map_sub,sub_apply]

theorem physicalLift_error (T S : FiberSpace →L[ℂ] FiberSpace) :
    ‖physicalLift M T-physicalLift M S‖ ≤ ‖T-S‖ := by
  rw [physicalLift_sub]
  exact physicalLift_norm M _

theorem physicalLift_power (T : FiberSpace →L[ℂ] FiberSpace) (u : FiberSpace) (n : ℕ) :
    (physicalLift M T^n) (embedding M u)=embedding M ((T^n) u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,ih,physicalLift_apply]

theorem embedding_normalize (u : FiberSpace) :
    embedding M (normalize u)=normalize (embedding M u) := by
  change embedding M (‖u‖⁻¹ • u)=‖embedding M u‖⁻¹ • embedding M u
  rw [embedding_norm,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem finiteIterate_physical {L : ℝ} (hL : 1 ≤ L)
    (c s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ellLength W ellRoot K P : ℕ) (hlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps N ellLength ≤ K) (v : FourierData) (n : ℕ) :
    embedding M (FourierData.iterate M c s z σ W ellRoot K P v n).value =
      (physicalLift M ((c : ℂ) • roundedSandwich M s z σ D hσ0 hσ W ellRoot K P)^n)
        (embedding M v.value) := by
  rw [FourierData.iterate_value M hL c s z σ D hσ0 hσ N ellLength W ellRoot K P hlog hK,
    physicalLift_power]

theorem normalizeData_physical_error (P : ℕ) (v : FourierData)
    (hsmall : (1/2 : ℝ)^P ≤ ‖v.value‖/2) :
    ‖embedding M (FourierData.normalizeData P v).value-normalize (embedding M v.value)‖ ≤
      2*(1/2 : ℝ)^P/‖v.value‖ := by
  rw [← embedding_normalize,← map_sub,embedding_norm]
  exact (FourierData.normalizeData_error P v hsmall).2

#print axioms finiteIterate_physical
#print axioms normalizeData_physical_error

end Maxwell.Continuum.Calibration.Supercell
