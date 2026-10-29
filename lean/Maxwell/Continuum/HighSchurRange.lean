import Maxwell.Continuum.HighSchurKernel

/-! The range of the actual high-block operator is a continuous preimage
of the finite Schur range. This proves closed range even at a crossing. -/

noncomputable section

namespace Maxwell.Continuum.HighSchur

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {L K : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
variable (R : BoundedInverse A)

def rangeSource : Ambient L K →L[ℂ] L :=
  WithLp.fstL 2 ℂ L K - B.adjoint.comp (R.map.comp (WithLp.sndL 2 ℂ L K))

theorem mem_range_iff (f : Ambient L K) :
    f ∈ (block D B A).toFun.range ↔ rangeSource B R f ∈ (schur D B R).range := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨low A u, ((block_equation_iff D B R u
      (block D B A u).ofLp.1 (block D B A u).ofLp.2).mp rfl).1⟩
  · rintro ⟨x, hx⟩
    let u : domain (L := L) A :=
      ⟨WithLp.toLp 2 (x, R.map (f.ofLp.2 - B x)), R.mem_domain _⟩
    refine ⟨u, (block_equation_iff D B R u f.ofLp.1 f.ofLp.2).mpr ?_⟩
    exact ⟨hx, rfl⟩

theorem range_eq_preimage :
    ((block D B A).toFun.range : Set (Ambient L K)) =
      (rangeSource B R) ⁻¹' ((schur D B R).range : Set L) := by
  ext f
  exact mem_range_iff D B R f

include R in
/-- Finite low dimension forces closed full range, including at singular
parameters. No coercivity or invertibility of the low block is assumed. -/
theorem range_isClosed [FiniteDimensional ℂ L] :
    IsClosed ((block D B A).toFun.range : Set (Ambient L K)) := by
  rw [range_eq_preimage D B R]
  exact (schur D B R).range.closed_of_finiteDimensional.preimage (rangeSource B R).continuous

end Maxwell.Continuum.HighSchur
