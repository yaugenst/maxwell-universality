import Maxwell.Continuum.CalibrationGlobalModeData

/-! The real/imaginary matrix coordinates have exactly the finite rational
Fourier norm used by the literal mode normalization. -/

namespace Maxwell.Continuum.Calibration.GlobalPower

open FreeFiber PeriodicSampling
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def cubeEquiv (R : ℕ) :
    (Fin (aliasSide R)×Fin (aliasSide R)×Fin (aliasSide R))≃
      {ν : Alias // ν∈Product.frequencyCube R} where
  toFun i := ⟨arrayAlias R i,by simpa only [Product.mem_frequencyCube,aliasInCube] using arrayAlias_mem R i⟩
  invFun ν := arrayAliasIndex R ν.1 (by simpa only [Product.mem_frequencyCube,aliasInCube] using ν.2)
  left_inv i := arrayIndex_alias R i
  right_inv ν := Subtype.ext (arrayAlias_index R ν.1 _)

theorem sum_array_alias (R : ℕ) (g : Alias → ℚ) :
    (∑ i : Fin (aliasSide R)×Fin (aliasSide R)×Fin (aliasSide R),g (arrayAlias R i))=
      ∑ ν∈Product.frequencyCube R,g ν := by
  have h := (cubeEquiv R).sum_comp (fun ν => g ν.1)
  exact h.trans (Finset.sum_coe_sort _ _)

theorem entry_norm_sum (R : ℕ) (f : RationalAliasField) :
    (∑ i : Fin (aliasArraySize R),((entry R f i).1^2+(entry R f i).2^2))=
      rationalNormSq f R := by
  rw [←(aliasArrayEquiv R).sum_comp (fun i => (entry R f i).1^2+(entry R f i).2^2)]
  simp only [Fintype.sum_prod_type,entry,Equiv.symm_apply_apply]
  simpa only [Fintype.sum_prod_type,rationalNormSq] using
    sum_array_alias R (fun ν => ∑ j : Fin 3,((f ν j).1^2+(f ν j).2^2))

theorem sample_norm (R : ℕ) (f : RationalAliasField) :
    (∑ i : Fin (2*aliasArraySize R),(sample R f i)^2)=rationalNormSq f R := by
  rw [←(realIndex R).sum_comp (fun i => (sample R f i)^2)]
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [sample_real,sample_imag,←Finset.sum_add_distrib]
  exact entry_norm_sum R f

theorem embed_norm (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) :
    rationalNormSq (embed R x) R=∑ i,x i^2 := by
  rw [←sample_norm,sample_embed]

theorem normCenter_unpack (R P : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) :
    FourierData.normCenter P ⟨R,unpack R x⟩=sqrtRationalCenter (∑ i,x i^2) P := by
  change sqrtRationalCenter (rationalNormSq (embed R x) R) P=_
  rw [embed_norm]

theorem rawMode_normCenter (L r N : ℕ) (z : ℚ) :
    FourierData.normCenter (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rawMode L r N z)=
      sqrtRationalCenter (∑ i,
        (PowerMachine.rationalPower (modeMatrix L r N z)
          (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field)
          (FiniteAlgorithm.iterations N) i)^2) (FiniteAlgorithm.precision L r N) := by
  rw [←rawModeData_eq]
  exact normCenter_unpack _ _ _

#print axioms sample_norm
#print axioms rawMode_normCenter

end Maxwell.Continuum.Calibration.GlobalPower
