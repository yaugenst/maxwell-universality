import Maxwell.Spectral.SimpleSplitting

namespace Maxwell.Spectral.SimpleSplitting

noncomputable section

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

def reflectionBlock (b : OrthonormalBasis ι ℂ H) (i : ι) (J : H ≃ₗᵢ[ℂ] H) :
    (ℂ × Complement i) →L[ℂ] (ℂ × Complement i) :=
  (decomposition b i).symm.toContinuousLinearMap.comp
    (J.toContinuousLinearMap.comp (decomposition b i).toContinuousLinearMap)

def complementReflection (b : OrthonormalBasis ι ℂ H) (i : ι) (J : H ≃ₗᵢ[ℂ] H) :
    Complement i →L[ℂ] Complement i :=
  (ContinuousLinearMap.snd ℂ ℂ (Complement i)).comp
    ((reflectionBlock b i J).comp (ContinuousLinearMap.inr ℂ ℂ (Complement i)))

theorem reflectionBlock_first (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (z : ℂ × Complement i) :
    (reflectionBlock b i J z).1 = z.1 := by
  change ((decomposition b i).symm (J (decomposition b i z))).1 = _
  rw [decomposition_symm_fst]
  have hi : inner ℂ (b i) (J (decomposition b i z)) =
      inner ℂ (b i) (decomposition b i z) := by
    conv_lhs => lhs; rw [← hfix]
    exact J.inner_map_map _ _
  rw [hi, ← decomposition_symm_fst, (decomposition b i).symm_apply_apply]

theorem reflectionBlock_one_zero (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) :
    reflectionBlock b i J (1, 0) = (1, 0) := by
  change (decomposition b i).symm (J (decomposition b i (1, 0))) = _
  rw [decomposition_one_zero, hfix, ← decomposition_one_zero b i]
  exact (decomposition b i).symm_apply_apply _

/-- A unitary symmetry fixing the distinguished eigenvector acts trivially
on its scalar coordinate and preserves its orthogonal complement. -/
theorem reflectionBlock_apply (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (z : ℂ × Complement i) :
    reflectionBlock b i J z = (z.1, complementReflection b i J z.2) := by
  apply Prod.ext
  · exact reflectionBlock_first b i J hfix z
  · have hsplit : z = z.1 • ((1 : ℂ), (0 : Complement i)) + (0, z.2) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, reflectionBlock_one_zero b i J hfix]
    simp [complementReflection]

theorem reflection_intertwining (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (z : ℂ × Complement i) :
    J (decomposition b i z) =
      decomposition b i (z.1, complementReflection b i J z.2) := by
  apply (decomposition b i).symm.injective
  rw [(decomposition b i).symm_apply_apply]
  exact reflectionBlock_apply b i J hfix z

theorem complementReflection_norm (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (v : Complement i) :
    ‖complementReflection b i J v‖ = ‖v‖ := by
  have h := congrArg (fun x : H => ‖x‖ ^ 2)
    (reflection_intertwining b i J hfix (0, v))
  rw [J.norm_map, decomposition_norm_sq, decomposition_norm_sq] at h
  simpa only [norm_zero, zero_pow (by omega : 2 ≠ 0), zero_add,
    sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h.symm

theorem complementReflection_involutive (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (hJ : Function.Involutive J) :
    Function.Involutive (complementReflection b i J) := by
  intro v
  have h := reflection_intertwining b i J hfix (0, complementReflection b i J v)
  rw [← reflection_intertwining b i J hfix (0, v), hJ] at h
  exact (congrArg Prod.snd ((decomposition b i).injective h)).symm

/-- The complementary reflection is a genuine unitary involution, obtained
from the physical symmetry rather than assumed in the eigenbranch chart. -/
def complementReflectionIsometry (b : OrthonormalBasis ι ℂ H) (i : ι)
    (J : H ≃ₗᵢ[ℂ] H) (hfix : J (b i) = b i) (hJ : Function.Involutive J) :
    Complement i ≃ₗᵢ[ℂ] Complement i where
  toLinearEquiv :=
    { (complementReflection b i J).toLinearMap with
      invFun := complementReflection b i J
      left_inv := complementReflection_involutive b i J hfix hJ
      right_inv := complementReflection_involutive b i J hfix hJ }
  norm_map' := complementReflection_norm b i J hfix

end
end Maxwell.Spectral.SimpleSplitting
