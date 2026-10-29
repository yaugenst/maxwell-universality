import Maxwell.Spectral.SectorSimplicity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace Maxwell.Spectral.FoldingInverse
open Matrix SectorSimplicity
noncomputable section
variable {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
  [DecidableEq α] [DecidableEq ι] [DecidableEq κ]

theorem unitary_sector_invertible (A : Matrix κ κ ℂ)
    (B : α → Matrix ι ι ℂ) (U : Matrix κ (ι × α) ℂ)
    (hleft : U.conjTranspose*U=1) (hright : U*U.conjTranspose=1)
    (hinter : A*U=U*sectorDiagonal B) (E : ℝ)
    (hsector : ∀ a, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (B a)-(E:ℂ) • 1).IsInvertible) :
    (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A-(E:ℂ) • 1).IsInvertible := by
  let e := matrixUnitaryEquiv U hleft hright
  have he (x : EuclideanSpace ℂ (ι × α)) :
      A.toEuclideanLin (e x) = e ((sectorDiagonal B).toEuclideanLin x) := by
    change A.toEuclideanLin (U.toEuclideanLin x) =
      U.toEuclideanLin ((sectorDiagonal B).toEuclideanLin x)
    have hh := congrArg (fun M : Matrix κ (ι × α) ℂ => M.toEuclideanLin x) hinter
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,LinearMap.comp_apply] using hh
  let F := Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A-(E:ℂ) • 1
  have hker (x : EuclideanSpace ℂ κ) (hx : F x=0) : x=0 := by
    have hAx : A.toEuclideanLin x=(E:ℂ) • x := by
      apply sub_eq_zero.mp
      exact hx
    have hy : (sectorDiagonal B).toEuclideanLin (e.symm x)=(E:ℂ) • e.symm x := by
      apply e.injective
      rw [← he,e.apply_symm_apply,e.map_smul,e.apply_symm_apply,hAx]
    have hz : e.symm x=0 := by
      ext ⟨i,a⟩
      have ha := sectorComponent_eigenvector B (E:ℂ) (e.symm x) hy a
      obtain ⟨ea,hea⟩ := hsector a
      have hez : ea (sectorComponent a (e.symm x))=ea 0 := by
        change ea.toContinuousLinearMap _=ea.toContinuousLinearMap 0
        rw [hea,map_zero]
        exact sub_eq_zero.mpr ha
      have hcomp := ea.injective hez
      exact congrArg (fun v : EuclideanSpace ℂ ι => v i) hcomp
    have hx0 := congrArg e hz
    simpa only [e.apply_symm_apply,map_zero] using hx0
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    exact LinearMap.ker_eq_bot'.mpr hker
  let eqv := ContinuousLinearEquiv.ofBijective F
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (F.toLinearMap.injective_iff_surjective.mp hinj))
  exact ⟨eqv,rfl⟩

theorem conventional_invertible_of_primitive (k : PeriodicYee.Momentum) (E : ℝ)
    (hsector : ∀ a : Folding.Coset,
      (Matrix.toEuclideanCLM (n := PrimitiveYee.Electric) (𝕜 := ℂ)
        (PrimitiveYee.fiber Concrete.material (Folding.sectorMomentum k a))-(E:ℂ) • 1).IsInvertible) :
    (Matrix.toEuclideanCLM (n := PeriodicYee.Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber Concrete.material (Folding.conventionalMomentum k))-(E:ℂ) • 1).IsInvertible :=
  unitary_sector_invertible _ _ (Folding.foldingMatrix k)
    (Concrete.primitive_folding_unitary k).1 (Concrete.primitive_folding_unitary k).2
    (Concrete.primitive_folding_intertwining k) E hsector

end
end Maxwell.Spectral.FoldingInverse
