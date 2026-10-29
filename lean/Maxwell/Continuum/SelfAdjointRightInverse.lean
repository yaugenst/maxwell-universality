import Maxwell.Continuum.SelfAdjointResolventData

/-! An everywhere-defined bounded right inverse of a self-adjoint partial
operator is automatically its two-sided inverse. -/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem injective_of_surjective (A : H →ₗ.[𝕜] H) (hA : IsSelfAdjoint A)
    (hs : Function.Surjective A) : Function.Injective A := by
  apply LinearPMap.ker_eq_bot.mp
  have hr : A.toFun.range = ⊤ := LinearMap.range_eq_top.mpr hs
  have ho := orthogonal_range_eq_adjoint_ker A hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA, hr, Submodule.top_orthogonal_eq_bot] at ho
  exact ho.symm

def BoundedInverse.ofRightInverse (A : H →ₗ.[𝕜] H) (hA : IsSelfAdjoint A)
    (R : H →L[𝕜] H) (hm : ∀ f, R f ∈ A.domain)
    (he : ∀ f, A ⟨R f, hm f⟩ = f) : BoundedInverse A where
  map := R
  mem_domain := hm
  apply_map := he
  map_apply x := congrArg Subtype.val
    (injective_of_surjective A hA (fun f => ⟨⟨R f, hm f⟩, he f⟩) (he (A x)))

end Maxwell.Continuum.SelfAdjointResolvent
