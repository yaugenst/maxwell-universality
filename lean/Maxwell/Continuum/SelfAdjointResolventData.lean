import Maxwell.Continuum.SelfAdjointResolventShift

/-!
# The genuine bounded resolvent of a partial operator

Membership in the real resolvent set means that the shifted partial operator
has an everywhere-defined bounded two-sided inverse taking values in its
actual domain. The identities here follow from those literal inverse laws.
-/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A bounded inverse on the ambient Hilbert space, with its domain and
both inverse laws recorded explicitly. -/
structure BoundedInverse (A : H →ₗ.[𝕜] H) where
  map : H →L[𝕜] H
  mem_domain : ∀ f, map f ∈ A.domain
  apply_map : ∀ f, A ⟨map f, mem_domain f⟩ = f
  map_apply : ∀ x : A.domain, map (A x) = (x : H)

namespace BoundedInverse

variable {A : H →ₗ.[𝕜] H}

theorem unique_map (R S : BoundedInverse A) : R.map = S.map := by
  ext f
  calc
    R.map f = R.map (A ⟨S.map f, S.mem_domain f⟩) := congrArg R.map (S.apply_map f).symm
    _ = S.map f := R.map_apply ⟨S.map f, S.mem_domain f⟩

theorem map_injective (R : BoundedInverse A) : Function.Injective R.map := by
  intro f g h
  have he : (⟨R.map f, R.mem_domain f⟩ : A.domain) = ⟨R.map g, R.mem_domain g⟩ :=
    Subtype.ext h
  have := congrArg A he
  simpa only [R.apply_map] using this

variable [CompleteSpace H]

theorem map_selfAdjoint (R : BoundedInverse A) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint R.map := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  have hformal := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hformal
  intro f g
  change inner 𝕜 (R.map f) g = inner 𝕜 f (R.map g)
  have h := hformal ⟨R.map f, R.mem_domain f⟩ ⟨R.map g, R.mem_domain g⟩
  simpa only [R.apply_map] using h.symm

/-- Construct genuine inverse data from the previously proved lower-bound theorem. -/
def ofLowerBound (hA : IsSelfAdjoint A) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ x : A.domain, δ * ‖(x : H)‖ ≤ ‖A x‖) : BoundedInverse A where
  map := inverse A hδ hbound hA
  mem_domain := inverse_mem_domain A hδ hbound hA
  apply_map := apply_inverse A hδ hbound hA
  map_apply := inverse_apply A hδ hbound hA

end BoundedInverse

/-- The usual real resolvent set, with bounded inverses required on all of L². -/
def realResolventSet (A : H →ₗ.[𝕜] H) : Set ℝ :=
  {σ | Nonempty (BoundedInverse (shift A σ))}

/-- The real spectrum is the complement of the actual real resolvent set. -/
def realSpectrum (A : H →ₗ.[𝕜] H) : Set ℝ := (realResolventSet A)ᶜ

@[simp] theorem not_mem_realSpectrum (A : H →ₗ.[𝕜] H) (σ : ℝ) :
    σ ∉ realSpectrum A ↔ Nonempty (BoundedInverse (shift A σ)) := by
  simp only [realSpectrum, realResolventSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]

/-- The first resolvent identity for genuine unbounded-operator inverses. -/
theorem resolvent_identity (A : H →ₗ.[𝕜] H) (σ τ : ℝ)
    (R : BoundedInverse (shift A σ)) (S : BoundedInverse (shift A τ)) :
    S.map - R.map = ((τ - σ : ℝ) : 𝕜) • (R.map * S.map) := by
  ext f
  have hS := S.apply_map f
  rw [shift_apply] at hS
  change A ⟨S.map f, S.mem_domain f⟩ - (τ : 𝕜) • S.map f = f at hS
  have hshift : shift A σ ⟨S.map f, S.mem_domain f⟩ =
      f + ((τ - σ : ℝ) : 𝕜) • S.map f := by
    calc
      shift A σ ⟨S.map f, S.mem_domain f⟩ =
          (A ⟨S.map f, S.mem_domain f⟩ - (τ : 𝕜) • S.map f) +
            ((τ - σ : ℝ) : 𝕜) • S.map f := by
        rw [shift_apply, RCLike.ofReal_sub, sub_smul]
        abel
      _ = f + ((τ - σ : ℝ) : 𝕜) • S.map f := by rw [hS]
  have h := R.map_apply ⟨S.map f, S.mem_domain f⟩
  rw [hshift, map_add, map_smul] at h
  change R.map f + ((τ - σ : ℝ) : 𝕜) • R.map (S.map f) = S.map f at h
  change S.map f - R.map f = ((τ - σ : ℝ) : 𝕜) • R.map (S.map f)
  exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))

/-- The second order of the product gives the same resolvent identity. -/
theorem resolvent_identity_reverse (A : H →ₗ.[𝕜] H) (σ τ : ℝ)
    (R : BoundedInverse (shift A σ)) (S : BoundedInverse (shift A τ)) :
    S.map - R.map = ((τ - σ : ℝ) : 𝕜) • (S.map * R.map) := by
  have h := resolvent_identity A τ σ S R
  have hn := congrArg Neg.neg h
  simpa only [neg_sub, neg_smul, ← neg_smul, ← RCLike.ofReal_neg, neg_sub] using hn

end Maxwell.Continuum.SelfAdjointResolvent
