import Maxwell.Continuum.HighSchur

/-! A bounded full-block inverse is constructed from high-block inversion and
bijectivity of the effective low Schur operator. -/

noncomputable section

namespace Maxwell.Continuum.HighSchur

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {L K : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : L →L[ℂ] L) (B : L →L[ℂ] K) {A : K →ₗ.[ℂ] K}
variable (R : BoundedInverse A) (hS : Function.Bijective (schur D B R))

/-- Bijectivity constructs the continuous low inverse. -/
def schurEquiv : L ≃L[ℂ] L :=
  ContinuousLinearEquiv.ofBijective (schur D B R)
    (LinearMap.ker_eq_bot.mpr hS.1) (LinearMap.range_eq_top.mpr hS.2)

def lowSolution : Ambient L K →L[ℂ] L :=
  (schurEquiv D B R hS).symm.toContinuousLinearMap.comp
    (WithLp.fstL 2 ℂ L K - B.adjoint.comp (R.map.comp (WithLp.sndL 2 ℂ L K)))

/-- Explicit block Gaussian elimination, as an everywhere bounded L² map. -/
def inverseMap : Ambient L K →L[ℂ] Ambient L K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ L K).symm.toContinuousLinearMap.comp
    ((lowSolution D B R hS).prod
      (R.map.comp (WithLp.sndL 2 ℂ L K - B.comp (lowSolution D B R hS))))

@[simp] theorem inverseMap_fst (f : Ambient L K) :
    (inverseMap D B R hS f).ofLp.1 = lowSolution D B R hS f := rfl

@[simp] theorem inverseMap_snd (f : Ambient L K) :
    (inverseMap D B R hS f).ofLp.2 = R.map (f.ofLp.2 - B (lowSolution D B R hS f)) := rfl

theorem inverseMap_mem_domain (f : Ambient L K) : inverseMap D B R hS f ∈ domain A :=
  R.mem_domain _

theorem block_inverseMap (f : Ambient L K) :
    block D B A ⟨inverseMap D B R hS f, inverseMap_mem_domain D B R hS f⟩ = f := by
  apply (block_equation_iff D B R _ f.ofLp.1 f.ofLp.2).mpr
  constructor
  · exact (schurEquiv D B R hS).apply_symm_apply _
  · rfl

theorem inverseMap_block (u : domain (L := L) A) :
    inverseMap D B R hS (block D B A u) = (u : Ambient L K) := by
  have he := (block_equation_iff D B R u
    (block D B A u).ofLp.1 (block D B A u).ofLp.2).mp rfl
  have hlo : lowSolution D B R hS (block D B A u) = low A u := by
    calc
      lowSolution D B R hS (block D B A u) =
          (schurEquiv D B R hS).symm (schur D B R (low A u)) :=
        congrArg (schurEquiv D B R hS).symm he.1.symm
      _ = low A u := (schurEquiv D B R hS).symm_apply_apply _
  apply (WithLp.equiv 2 (L × K)).injective
  apply Prod.ext
  · exact hlo
  · change R.map ((block D B A u).ofLp.2 - B (lowSolution D B R hS (block D B A u))) =
      (high A u : K)
    rw [hlo]
    exact he.2.symm

/-- No inverse of the full operator is assumed: the previous two literal
identities construct one from the high inverse and low Schur bijectivity. -/
def blockInverse : BoundedInverse (block D B A) where
  map := inverseMap D B R hS
  mem_domain := inverseMap_mem_domain D B R hS
  apply_map := block_inverseMap D B R hS
  map_apply := inverseMap_block D B R hS

include R hS in
theorem block_has_boundedInverse : Nonempty (BoundedInverse (block D B A)) :=
  ⟨blockInverse D B R hS⟩

end Maxwell.Continuum.HighSchur
