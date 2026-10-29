import Maxwell.Continuum.SelfAdjointResolventData
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Exact Schur elimination of an unbounded high block

The block operator acts on the Hilbert product of low and high spaces, with
the literal domain `L × D(A)`. Eliminating the high component uses a genuine
bounded inverse of A, including its domain membership and both inverse laws.
-/

noncomputable section

namespace Maxwell.Continuum.HighSchur

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {L K : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Ambient (L K : Type*) := WithLp 2 (L × K)

/-- Exactly the high operator's domain in the Hilbert product. -/
def domain (A : K →ₗ.[ℂ] K) : Submodule ℂ (Ambient L K) :=
  A.domain.comap (WithLp.sndL 2 ℂ L K).toLinearMap

def low (A : K →ₗ.[ℂ] K) : domain (L := L) A →ₗ[ℂ] L :=
  (WithLp.fstL 2 ℂ L K).toLinearMap.comp (domain A).subtype

def high (A : K →ₗ.[ℂ] K) : domain (L := L) A →ₗ[ℂ] A.domain :=
  ((WithLp.sndL 2 ℂ L K).toLinearMap.comp (domain A).subtype).codRestrict A.domain
    (fun x => x.property)

/-- The actual unbounded Hermitian block expression, on its full domain. -/
def block (D : L →L[ℂ] L) (B : L →L[ℂ] K) (A : K →ₗ.[ℂ] K) :
    Ambient L K →ₗ.[ℂ] Ambient L K where
  domain := domain A
  toFun := (WithLp.linearEquiv 2 ℂ (L × K)).symm.toLinearMap.comp
    ((D.toLinearMap.comp (low A) +
        B.adjoint.toLinearMap.comp (A.domain.subtype.comp (high A))).prod
      (B.toLinearMap.comp (low A) + A.toFun.comp (high A)))

@[simp] theorem block_domain (D : L →L[ℂ] L) (B : L →L[ℂ] K) (A : K →ₗ.[ℂ] K) :
    (block D B A).domain = domain A := rfl

@[simp] theorem block_apply (D : L →L[ℂ] L) (B : L →L[ℂ] K) (A : K →ₗ.[ℂ] K)
    (u : domain (L := L) A) :
    block D B A u = WithLp.toLp 2
      (D (low A u) + B.adjoint (high A u), B (low A u) + A (high A u)) := rfl

/-- The effective low operator after exact elimination. -/
def schur (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
    (R : BoundedInverse A) : L →L[ℂ] L :=
  D - B.adjoint.comp (R.map.comp B)

@[simp] theorem schur_apply (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
    (R : BoundedInverse A) (x : L) :
    schur D B R x = D x - B.adjoint (R.map (B x)) := rfl

/-- Exact Schur reduction for an arbitrary source, including the high-domain equation. -/
theorem block_equation_iff (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
    (R : BoundedInverse A) (u : domain (L := L) A) (f : L) (g : K) :
    block D B A u = WithLp.toLp 2 (f, g) ↔
      schur D B R (low A u) = f - B.adjoint (R.map g) ∧
        (high A u : K) = R.map (g - B (low A u)) := by
  constructor
  · intro hu
    have hf := congrArg (fun v : Ambient L K => v.ofLp.1) hu
    have hg := congrArg (fun v : Ambient L K => v.ofLp.2) hu
    change D (low A u) + B.adjoint (high A u) = f at hf
    change B (low A u) + A (high A u) = g at hg
    have ha : A (high A u) = g - B (low A u) := by
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hg)
    have hy : (high A u : K) = R.map (g - B (low A u)) :=
      (R.map_apply (high A u)).symm.trans (congrArg R.map ha)
    refine ⟨?_, hy⟩
    rw [hy, map_sub, map_sub] at hf
    rw [schur_apply]
    have h := congrArg (fun z => z - B.adjoint (R.map g)) hf
    abel_nf at h ⊢
    exact h
  · rintro ⟨hf, hy⟩
    have he : high A u = ⟨R.map (g - B (low A u)), R.mem_domain _⟩ := Subtype.ext hy
    have ha : A (high A u) = g - B (low A u) :=
      (congrArg A he).trans (R.apply_map _)
    apply (WithLp.equiv 2 (L × K)).injective
    apply Prod.ext
    · change D (low A u) + B.adjoint (high A u) = f
      rw [hy, map_sub, map_sub]
      rw [schur_apply] at hf
      have h := congrArg (fun z => z + B.adjoint (R.map g)) hf
      abel_nf at h ⊢
      exact h
    · change B (low A u) + A (high A u) = g
      rw [ha]
      abel

/-- The full block kernel is the graph over the effective low kernel. -/
theorem block_kernel_iff (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
    (R : BoundedInverse A) (u : domain (L := L) A) :
    block D B A u = 0 ↔
      schur D B R (low A u) = 0 ∧ (high A u : K) = -R.map (B (low A u)) := by
  simpa only [map_zero, map_neg, zero_sub, sub_zero,
    show WithLp.toLp 2 ((0 : L), (0 : K)) = (0 : Ambient L K) from rfl]
    using block_equation_iff D B R u 0 0

end Maxwell.Continuum.HighSchur
