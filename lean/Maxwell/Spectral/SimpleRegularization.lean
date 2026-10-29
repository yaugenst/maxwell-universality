import Maxwell.Spectral.SimpleSplitting
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace Maxwell.Spectral.SimpleSplitting

noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H] [CompleteSpace H]

/-- Adding the selected rank-one spectral projector removes the sole zero
eigenvalue of the shifted operator. -/
theorem simple_regularization_invertible
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℂ H))
    (hsimple : ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i) :
    (T - (hT.eigenvalues rfl i : ℂ) • 1 +
      (innerSL ℂ (hT.eigenvectorBasis rfl i)).smulRight
        (hT.eigenvectorBasis rfl i)).IsInvertible := by
  let b := hT.eigenvectorBasis rfl
  let A := T - (hT.eigenvalues rfl i : ℂ) • 1 + (innerSL ℂ (b i)).smulRight (b i)
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply b.repr.injective
    ext j
    have hh := congrArg (fun x : H => b.repr x j) hv
    change b.repr (T v - (hT.eigenvalues rfl i : ℂ) • v + inner ℂ (b i) v • b i) j =
      b.repr 0 j at hh
    simp only [map_add, map_sub, map_smul, map_zero, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] at hh
    rw [show b.repr (T v) j = (hT.eigenvalues rfl j : ℂ) * b.repr v j from
      hT.eigenvectorBasis_apply_self_apply rfl v j, b.repr_self] at hh
    simp only [map_zero, PiLp.zero_apply]
    by_cases hj : j = i
    · subst j
      simpa only [PiLp.single_apply, ite_true, mul_one, sub_self, zero_add,
        ← OrthonormalBasis.repr_apply_apply] using hh
    · have hn : (hT.eigenvalues rfl j : ℂ) - (hT.eigenvalues rfl i : ℂ) ≠ 0 := by
        exact sub_ne_zero.mpr (Complex.ofReal_injective.ne (hsimple j hj))
      have hz : ((hT.eigenvalues rfl j : ℂ) - (hT.eigenvalues rfl i : ℂ)) * b.repr v j = 0 := by
        simpa only [PiLp.single_apply, ite_eq_right_iff.mpr (fun h => (hj h).elim),
          mul_zero, add_zero, sub_mul] using hh
      exact (mul_eq_zero.mp hz).resolve_left hn
  exact ⟨ContinuousLinearEquiv.ofBijective A hker
    (LinearMap.range_eq_top.mpr
      (A.toLinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))), rfl⟩

end
end Maxwell.Spectral.SimpleSplitting
