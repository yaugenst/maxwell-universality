import Maxwell.Spectral.SimpleReflection

namespace Maxwell.Spectral.SimpleSplitting

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]

/-- An involutive unitary symmetry commuting with a Hermitian operator acts
by a proved sign on each simple eigenspace. -/
theorem simple_eigenvector_parity (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H))
    (hsimple : ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i)
    (J : H ≃ₗᵢ[ℂ] H) (hJ : Function.Involutive J)
    (hcommute : ∀ x, T (J x) = J (T x)) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      J (hT.eigenvectorBasis rfl i) = σ • hT.eigenvectorBasis rfl i := by
  let b := hT.eigenvectorBasis rfl
  let u := b i
  let σ := inner ℂ u (J u)
  have hu : T u = (hT.eigenvalues rfl i : ℂ) • u := by
    simpa only [u, b, RCLike.ofReal_eq_complex_ofReal] using hT.apply_eigenvectorBasis rfl i
  have hv : J u - σ • u = 0 := by
    apply simple_complement_kernel T hT i hsimple
    · change inner ℂ u (J u - σ • u) = 0
      rw [inner_sub_right, inner_smul_right]
      have hunit : inner ℂ u u = 1 := b.inner_eq_one i
      rw [hunit, mul_one]
      exact sub_self σ
    · rw [map_sub, map_smul, hcommute, hu, J.map_smul]
      module
  have hparity : J u = σ • u := sub_eq_zero.mp hv
  have hs : σ * σ = 1 := by
    have hh := congrArg J hparity
    rw [hJ, J.map_smul, hparity, smul_smul] at hh
    have hi := congrArg (inner ℂ u) hh
    rw [inner_smul_right] at hi
    have hunit : inner ℂ u u = 1 := b.inner_eq_one i
    rw [hunit, mul_one] at hi
    exact hi.symm
  exact ⟨σ, mul_self_eq_one_iff.mp hs, hparity⟩

end
end Maxwell.Spectral.SimpleSplitting
