import Maxwell.Continuum.FiberL1Neumann
import Maxwell.Continuum.ClusterComplementDimension

/-! Finite central-cluster forcing is absolutely summable with an explicit
bound derived from the actual eight-alias support of the 16-dimensional cluster. -/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber ClusterComplement
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

def centralFinset : Finset Alias :=
  Finset.univ.map ⟨Subtype.val, Subtype.val_injective⟩
  (α := CentralAlias)

@[simp] theorem mem_centralFinset (ν : Alias) : ν ∈ centralFinset ↔ IsCentralAlias ν := by
  simp [centralFinset]

@[simp] theorem centralFinset_card : centralFinset.card = 8 := by
  simp [centralFinset, centralAlias_card]

theorem cluster_memℓ1 (u : FiberSpace) :
    Memℓp (fun ν => ClusterComplement.clusterProjection u ν) 1 := by
  apply (memℓp_zero (E := fun _ : Alias => Polarization) ?_).of_exponent_ge (by norm_num)
  apply centralAliases_finite.subset
  intro ν hν
  by_contra hn
  exact hν (by rw [ClusterComplement.clusterProjection_apply, clusterBlock_noncentral ν hn, zero_apply])

def clusterLiftLinear : FiberSpace →ₗ[ℂ] Space where
  toFun u := ⟨fun ν => ClusterComplement.clusterProjection u ν, cluster_memℓ1 u⟩
  map_add' u v := by apply Subtype.ext; funext ν; simp only [map_add]; rfl
  map_smul' a u := by apply Subtype.ext; funext ν; simp only [map_smul]; rfl

@[simp] theorem clusterLiftLinear_apply (u : FiberSpace) (ν : Alias) :
    clusterLiftLinear u ν = ClusterComplement.clusterProjection u ν := rfl

theorem clusterLiftLinear_norm_le_projection (u : FiberSpace) :
    ‖clusterLiftLinear u‖ ≤ 8 * ‖ClusterComplement.clusterProjection u‖ := by
  rw [norm_eq_tsum]
  calc
    (∑' ν, ‖clusterLiftLinear u ν‖) = ∑ ν ∈ centralFinset, ‖clusterLiftLinear u ν‖ := by
      apply tsum_eq_sum
      intro ν hν
      have hn : ¬IsCentralAlias ν := by simpa only [mem_centralFinset] using hν
      rw [clusterLiftLinear_apply, ClusterComplement.clusterProjection_apply,
        clusterBlock_noncentral ν hn, zero_apply, norm_zero]
    _ ≤ ∑ _ν ∈ centralFinset, ‖ClusterComplement.clusterProjection u‖ := by
      apply Finset.sum_le_sum
      intro ν _
      exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        (ClusterComplement.clusterProjection u) ν
    _ = _ := by simp

theorem clusterLiftLinear_norm_le (u : FiberSpace) : ‖clusterLiftLinear u‖ ≤ 8 * ‖u‖ := by
  have hp : ‖ClusterComplement.clusterProjection u‖ ≤ ‖u‖ := by
    exact (ClusterComplement.clusterProjection.le_opNorm u).trans
      ((mul_le_mul_of_nonneg_right ClusterComplement.clusterProjection_norm_le
        (norm_nonneg u)).trans_eq (one_mul _))
  exact (clusterLiftLinear_norm_le_projection u).trans (mul_le_mul_of_nonneg_left hp (by norm_num))

def clusterLift : FiberSpace →L[ℂ] Space :=
  clusterLiftLinear.mkContinuous 8 clusterLiftLinear_norm_le

theorem inclusion_clusterLift (u : FiberSpace) :
    inclusion (clusterLift u) = ClusterComplement.clusterProjection u := rfl

theorem clusterLift_norm_le_projection (u : FiberSpace) :
    ‖clusterLift u‖ ≤ 8 * ‖ClusterComplement.clusterProjection u‖ :=
  clusterLiftLinear_norm_le_projection u

#print axioms clusterLift_norm_le_projection

end Maxwell.Continuum.FiberL1
