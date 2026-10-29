import Maxwell.Spectral.ClusterOrthonormalization

/-! Commuting symmetries preserve an isolated spectral cluster and the explicit
Gram--Schmidt frame constructed inside it. -/

namespace Maxwell.Spectral.ClusterProjection

noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A commuting map has no matrix entries between distinct eigenvalues. -/
theorem commuting_repr_zero (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : ι → ℝ) (hdiag : ∀ x i, b.repr (T x) i = (μ i : ℂ) * b.repr x i)
    (J : E →ₗ[ℂ] E) (hcommute : ∀ x, T (J x) = J (T x))
    (i j : ι) (hne : μ i ≠ μ j) : b.repr (J (b i)) j = 0 := by
  have heig : T (b i) = (μ i : ℂ) • b i := by
    apply b.repr.injective
    ext k
    simp only [hdiag, map_smul, PiLp.smul_apply, smul_eq_mul,
      OrthonormalBasis.repr_self, PiLp.single_apply]
    split_ifs with h
    · subst k
      rfl
    · simp
  have hh := congrArg (fun x => b.repr x j) (hcommute (b i))
  rw [hdiag, heig, J.map_smul] at hh
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at hh
  have hz : ((μ j : ℂ) - (μ i : ℂ)) * b.repr (J (b i)) j = 0 := by
    rw [sub_mul, hh, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (fun h => hne (Complex.ofReal_injective h.symm)))

/-- Separation only across the selected/complement boundary is sufficient;
eigenvalue multiplicity within the cluster is allowed. -/
theorem projection_commutes_of_separated (b : OrthonormalBasis ι ℂ E)
    (T : E →ₗ[ℂ] E) (μ : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (μ i : ℂ) * b.repr x i)
    (S : Finset ι) (hsep : ∀ i ∈ S, ∀ j ∉ S, μ i ≠ μ j)
    (J : E →ₗ[ℂ] E) (hcommute : ∀ x, T (J x) = J (T x)) (x : E) :
    projection b S (J x) = J (projection b S x) := by
  have hmaps : (projection b S).toLinearMap.comp J =
      J.comp (projection b S).toLinearMap := by
    apply b.toBasis.ext
    intro i
    change projection b S (J (b i)) = J (projection b S (b i))
    rw [projection_basis]
    apply b.repr.injective
    ext j
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, repr_projection]
      by_cases hj : j ∈ S
      · simp only [hj, ite_true]
      · simp only [hj, ite_false]
        exact (commuting_repr_zero b T μ hdiag J hcommute i j (hsep i hi j hj)).symm
    · simp only [hi, ite_false, map_zero, repr_projection, PiLp.zero_apply]
      by_cases hj : j ∈ S
      · simp only [hj, ite_true]
        exact commuting_repr_zero b T μ hdiag J hcommute i j (Ne.symm (hsep j hj i hi))
      · simp only [hj, ite_false]
  exact LinearMap.congr_fun hmaps x

end
end Maxwell.Spectral.ClusterProjection

namespace Maxwell.Spectral.ClusterOrthonormalization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every scalar combination in Gram--Schmidt retains the common symmetry
eigenvalue, including when the unnormalized inputs are degenerate. -/
theorem frame_parity (J : E →ₗ[ℂ] E) (σ : ℂ) (a b : E)
    (ha : J a = σ • a) (hb : J b = σ • b) (i : Fin 2) :
    J (frame a b i) = σ • frame a b i := by
  have hfirst : J (first a) = σ • first a := by
    simp only [first, unitVector]
    rw [J.map_smul, ha, smul_comm]
  have hrem : J (remainder a b) = σ • remainder a b := by
    rw [remainder, J.map_sub, J.map_smul, hb, hfirst, smul_sub, smul_comm]
  fin_cases i
  · exact hfirst
  · change J (unitVector (remainder a b)) = σ • unitVector (remainder a b)
    simp only [unitVector]
    rw [J.map_smul, hrem, smul_comm]

end
end Maxwell.Spectral.ClusterOrthonormalization
