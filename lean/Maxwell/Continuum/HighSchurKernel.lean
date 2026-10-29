import Maxwell.Continuum.HighSchurInverse
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Kernel multiplicities and bounded invertibility are preserved by exact
elimination of the high block. -/

noncomputable section

namespace Maxwell.Continuum.HighSchur

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {L K : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
variable (R : BoundedInverse A)

def kernelDomain : (block D B A).ker →ₗ[ℂ] domain (L := L) A :=
  Submodule.inclusion (block D B A).ker_le_domain

theorem kernelDomain_eq_zero (u : (block D B A).ker) :
    block D B A (kernelDomain D B u) = 0 :=
  LinearPMap.coe_mem_ker_iff.mp u.property

def kernelLow : (block D B A).ker →ₗ[ℂ] (schur D B R).ker :=
  ((low A).comp (kernelDomain D B)).codRestrict (schur D B R).ker (by
    intro u
    exact ((block_kernel_iff D B R (kernelDomain D B u)).mp (kernelDomain_eq_zero D B u)).1)

/-- The explicit graph map x ↦ (x,−A⁻¹Bx). -/
def kernelGraph : L →L[ℂ] Ambient L K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ L K).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ L).prod (-(R.map.comp B)))

omit [CompleteSpace L] [CompleteSpace K] in
theorem kernelGraph_mem_domain (x : L) : kernelGraph B R x ∈ domain A :=
  A.domain.neg_mem (R.mem_domain (B x))

theorem kernelGraph_mem_ker (x : (schur D B R).ker) : kernelGraph B R x ∈ (block D B A).ker := by
  apply (LinearPMap.coe_mem_ker_iff
    (x := ⟨kernelGraph B R x, kernelGraph_mem_domain B R x⟩)).mpr
  apply (block_kernel_iff D B R _).mpr
  exact ⟨x.property, rfl⟩

def kernelLift : (schur D B R).ker →ₗ[ℂ] (block D B A).ker :=
  ((kernelGraph B R).toLinearMap.comp (schur D B R).ker.subtype).codRestrict
    (block D B A).ker (kernelGraph_mem_ker D B R)

theorem kernelLow_lift (x : (schur D B R).ker) :
    kernelLow D B R (kernelLift D B R x) = x := by
  apply Subtype.ext
  rfl

theorem kernelLift_low (u : (block D B A).ker) :
    kernelLift D B R (kernelLow D B R u) = u := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (L × K)).injective
  apply Prod.ext
  · rfl
  · exact ((block_kernel_iff D B R (kernelDomain D B u)).mp
      (kernelDomain_eq_zero D B u)).2.symm

/-- Exact algebraic equivalence of the two kernels, preserving multiplicities. -/
def kernelEquiv : (block D B A).ker ≃ₗ[ℂ] (schur D B R).ker where
  __ := kernelLow D B R
  invFun := kernelLift D B R
  left_inv := kernelLift_low D B R
  right_inv := kernelLow_lift D B R

theorem kernel_finrank_eq :
    Module.finrank ℂ (block D B A).ker = Module.finrank ℂ (schur D B R).ker :=
  (kernelEquiv D B R).finrank_eq

/-- Full invertibility is equivalent to low Schur bijectivity; no
finite-dimensional assumption is needed for this equivalence. -/
theorem block_inverse_iff_schur_bijective :
    Nonempty (BoundedInverse (block D B A)) ↔ Function.Bijective (schur D B R) := by
  constructor
  · rintro ⟨Q⟩
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro x hx
      let y := kernelLift D B R ⟨x, hx⟩
      have hy := Q.map_apply (kernelDomain D B y)
      rw [kernelDomain_eq_zero, map_zero] at hy
      have hx0 := congrArg (fun v : Ambient L K => v.ofLp.1) hy
      change (0 : L) = x at hx0
      exact (Submodule.mem_bot ℂ).mpr hx0.symm
    · intro f
      let u : domain (L := L) A := ⟨Q.map (WithLp.toLp 2 (f, 0)), Q.mem_domain _⟩
      have he := (block_equation_iff D B R u f 0).mp (Q.apply_map _)
      exact ⟨low A u, by simpa only [map_zero, sub_zero] using he.1⟩
  · intro hS
    exact ⟨blockInverse D B R hS⟩

/-- For a finite low space, excluding a zero mode constructs the full
bounded inverse. Continuous spectrum near zero cannot remain hidden in the high block. -/
theorem block_inverse_iff_schur_ker_eq_bot [FiniteDimensional ℂ L] :
    Nonempty (BoundedInverse (block D B A)) ↔ (schur D B R).ker = ⊥ := by
  rw [block_inverse_iff_schur_bijective]
  constructor
  · exact fun h => LinearMap.ker_eq_bot.mpr h.1
  · intro h
    have hi := LinearMap.ker_eq_bot.mp h
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end Maxwell.Continuum.HighSchur
