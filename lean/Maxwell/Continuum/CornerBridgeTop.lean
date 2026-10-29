import Maxwell.Continuum.CornerBridgeAction
import Maxwell.Continuum.PeriodicPerturbation

/-!
# The actual normalized top corner state

The certified finite vector is transported into the literal continuum
cluster. Its eigenvalue equation, norm and the symmetry of the compressed
material operator are proved for the actual Hilbert-space operators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation
open scoped InnerProductSpace

theorem realCube_smul (r : ℝ) (u : Corner.ClusterField) :
    realCube (r • u) = (r : ℂ) • realCube u := by
  funext s j
  simp only [realCube,realMomentum,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]

theorem packReal_smul (r : ℝ) (u : Corner.ClusterField) :
    packReal (r • u) = (r : ℂ) • packReal u := by
  rw [packReal,realCube_smul,pack_smul]
  rfl

theorem cornerProjection_smul (r : ℝ) (u : Corner.ClusterField) :
    Corner.clusterProjection (r • u) = r • Corner.clusterProjection u := by
  funext s
  simp only [Corner.clusterProjection,Pi.smul_apply,Matrix.mulVec_smul]

theorem cornerOperator_smul (r : ℝ) (u : Corner.ClusterField) :
    Corner.clusterOperator (r • u) = r • Corner.clusterOperator u := by
  funext s
  simp only [Corner.clusterOperator,Pi.smul_apply,Matrix.mulVec_smul,
    Finset.smul_sum,smul_comm r]

theorem normalizedCorner_transverse :
    Corner.clusterProjection Corner.normalizedClusterVector = Corner.normalizedClusterVector := by
  rw [Corner.normalizedClusterVector,cornerProjection_smul,Corner.clusterProjection_embedding,
    Corner.projectedEmbedding,
    Corner.projection_mulVec_transverse _ Corner.normalizedTopVector_sum]

theorem normalizedCorner_eigen :
    Corner.clusterOperator Corner.normalizedClusterVector =
      Corner.lambdaStar • Corner.normalizedClusterVector := by
  have he : Corner.projectedEmbedding Corner.selectedParity Corner.normalizedTopVector =
      Corner.embedding Corner.selectedParity Corner.normalizedTopVector := by
    rw [Corner.projectedEmbedding,
      Corner.projection_mulVec_transverse _ Corner.normalizedTopVector_sum]
  rw [Corner.normalizedClusterVector,cornerOperator_smul,← he,
    Corner.clusterOperator_intertwines,Corner.normalizedTopVector_eigen,
    Corner.embedding_smul,he,smul_comm]

/-- The actual normalized eigenvector in the sixteen-dimensional subspace. -/
def topState : clusterSpace :=
  ⟨packReal Corner.normalizedClusterVector, (mem_clusterSpace_iff _).mpr (by
    rw [clusterProjection_packReal,normalizedCorner_transverse])⟩

theorem topState_norm : ‖topState‖ = 1 := by
  have h := packReal_inner Corner.normalizedClusterVector Corner.normalizedClusterVector
  rw [Corner.normalizedClusterVector_normSq,inner_self_eq_norm_sq_to_K] at h
  rw [← RCLike.ofReal_pow] at h
  have hr : ‖packReal Corner.normalizedClusterVector‖ ^ 2 = 1 :=
    RCLike.ofReal_injective h
  change ‖packReal Corner.normalizedClusterVector‖ = 1
  nlinarith [norm_nonneg (packReal Corner.normalizedClusterVector)]

theorem finiteK_apply (u : clusterSpace) :
    (finiteK u).val = clusterPotential u.val :=
  clusterProjection_clusterPotential u.val

theorem finiteK_topState : finiteK topState = (Corner.lambdaStar : ℂ) • topState := by
  apply Subtype.ext
  rw [finiteK_apply]
  change clusterPotential (packReal Corner.normalizedClusterVector) = _
  rw [clusterPotential_packReal,normalizedCorner_eigen,packReal_smul]
  rfl

theorem clusterPotential_isSymmetric : clusterPotential.IsSymmetric := by
  have hp (u v : FiberSpace) : inner ℂ (clusterProjection u) v = inner ℂ u (clusterProjection v) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      clusterProjection_isStarProjection.isSelfAdjoint) u v
  intro u v
  change inner ℂ (-(clusterProjection (potential (clusterProjection u)))) v =
    inner ℂ u (-(clusterProjection (potential (clusterProjection v))))
  rw [inner_neg_left,inner_neg_right,hp]
  have hv (x y : FiberSpace) : inner ℂ (potential x) y = inner ℂ x (potential y) :=
    potential_isSymmetric x y
  rw [hv,← hp]

theorem finiteK_isSymmetric : finiteK.IsSymmetric := by
  intro u v
  change inner ℂ (finiteK u).val v.val = inner ℂ u.val (finiteK v).val
  rw [finiteK_apply,finiteK_apply]
  exact clusterPotential_isSymmetric u.val v.val

theorem finiteK_norm_le : ‖finiteK‖ ≤ 7 := by
  apply (compress_norm_le clusterPotential).trans
  change ‖-(clusterProjection * potential * clusterProjection)‖ ≤ 7
  rw [norm_neg]
  exact (contraction_sandwich_norm_le _ _ _ clusterProjection_norm_le
    clusterProjection_norm_le).trans potential_norm_le

end Maxwell.Continuum.CornerBridge
