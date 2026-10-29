import Maxwell.Composition.BlockModes
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The complementary coordinates for an actual repeated unit local mode.
All reconstruction identities and contraction bounds are proved here,
rather than imposed on the full physical assembly as abstract assumptions. -/

noncomputable section

namespace Maxwell.Composition

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def modeRange (q : EuclideanSpace ℝ κ) : Submodule ℝ (EuclideanSpace ℝ (ι × κ)) :=
  (blockInjection (ι := ι) q).range

abbrev ModeComplement (q : EuclideanSpace ℝ κ) := (modeRange (ι := ι) q)ᗮ

def modeComplementInclusion (q : EuclideanSpace ℝ κ) :
    ModeComplement (ι := ι) q →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  ((modeRange (ι := ι) q)ᗮ).subtypeL

def modeComplementProjection (q : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] ModeComplement (ι := ι) q :=
  ((modeRange (ι := ι) q)ᗮ).orthogonalProjectionOnto

theorem blockInjection_adjoint_comp_self (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1) :
    (blockInjection (ι := ι) q).adjoint.comp (blockInjection q) = 1 := by
  have hnorm : ∀ g : EuclideanSpace ℝ ι,
      ‖blockInjection (ι := ι) q g‖ = ‖g‖ := by
    intro g
    rw [blockInjection_norm_apply, hq, one_mul]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (blockInjection (ι := ι) q)).mp hnorm

@[simp] theorem blockInjection_adjoint_cancel (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (g : EuclideanSpace ℝ ι) :
    (blockInjection q).adjoint (blockInjection q g) = g :=
  congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => T g)
    (blockInjection_adjoint_comp_self q hq)

theorem modeRange_projection (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (x : EuclideanSpace ℝ (ι × κ)) :
    (modeRange q).starProjection x =
      blockInjection q ((blockInjection q).adjoint x) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ) := blockInjection q
  change U.range.starProjection x = U (U.adjoint x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨U.adjoint x, rfl⟩
  · change x - U (U.adjoint x) ∈ U.rangeᗮ
    rw [ContinuousLinearMap.orthogonal_range]
    change U.adjoint (x - U (U.adjoint x)) = 0
    simp [U, hq]

theorem modeCoordinate_decomposition (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (x : EuclideanSpace ℝ (ι × κ)) :
    x = blockInjection q ((blockInjection q).adjoint x) +
      modeComplementInclusion q (modeComplementProjection q x) := by
  change x = blockInjection q ((blockInjection q).adjoint x) +
    ((modeRange (ι := ι) q)ᗮ).starProjection x
  rw [Submodule.starProjection_orthogonal_val, modeRange_projection q hq]
  abel

@[simp] theorem modeComplementProjection_injection (q : EuclideanSpace ℝ κ)
    (hq : ‖q‖ = 1) (g : EuclideanSpace ℝ ι) :
    modeComplementProjection q (blockInjection q g) = 0 := by
  apply Subtype.ext
  change ((modeRange (ι := ι) q)ᗮ).starProjection (blockInjection q g) = 0
  rw [Submodule.starProjection_orthogonal_val, modeRange_projection q hq,
    blockInjection_adjoint_cancel q hq, sub_self]

@[simp] theorem modeComplementProjection_inclusion (q : EuclideanSpace ℝ κ)
    (c : ModeComplement (ι := ι) q) :
    modeComplementProjection q (modeComplementInclusion q c) = c := by
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self c

@[simp] theorem modeAdjoint_inclusion (q : EuclideanSpace ℝ κ)
    (c : ModeComplement (ι := ι) q) :
    (blockInjection q).adjoint (modeComplementInclusion q c) = 0 := by
  have hc := c.property
  change (c : EuclideanSpace ℝ (ι × κ)) ∈ (blockInjection q).rangeᗮ at hc
  rw [ContinuousLinearMap.orthogonal_range] at hc
  exact hc

theorem modeInjection_norm_le (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1) :
    ‖blockInjection (ι := ι) q‖ ≤ 1 := by
  simpa only [hq] using blockInjection_norm_le (ι := ι) q

theorem modeAdjoint_norm_le (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1) :
    ‖(blockInjection (ι := ι) q).adjoint‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact modeInjection_norm_le q hq

theorem modeComplementInclusion_norm_le (q : EuclideanSpace ℝ κ) :
    ‖modeComplementInclusion (ι := ι) q‖ ≤ 1 :=
  Submodule.norm_subtypeL_le _

theorem modeComplementProjection_norm_le (q : EuclideanSpace ℝ κ) :
    ‖modeComplementProjection (ι := ι) q‖ ≤ 1 :=
  Submodule.orthogonalProjectionOnto_norm_le _

end Maxwell.Composition
