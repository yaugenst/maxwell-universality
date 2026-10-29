import Maxwell.Continuum.CornerBridgeGap
import Maxwell.Continuum.CornerBridgeHessianReal
import Maxwell.Continuum.CornerBridgeVelocity

/-!
# Actual corner complementary inverse and quadratic coefficients

The explicit finite resolvent vectors are identified with the genuine
bounded inverse on the orthogonal complement of the actual top state.
Their quadratic forms are the certified diagonal coefficients.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement PeriodicPerturbation
open scoped InnerProductSpace

def velocityState (j : Fin 3) : clusterSpace :=
  ⟨packReal (Corner.velocity j Corner.normalizedClusterVector), (mem_clusterSpace_iff _).mpr (by
    rw [clusterProjection_packReal,velocity_transverse])⟩

def resolventState (j : Fin 3) : clusterSpace :=
  ⟨packReal (resolventCube j), (mem_clusterSpace_iff _).mpr (by
    rw [clusterProjection_packReal,resolventCube_transverse])⟩

theorem velocityState_perp (j : Fin 3) : inner ℂ topState (velocityState j) = 0 := by
  change inner ℂ (packReal Corner.normalizedClusterVector)
    (packReal (Corner.velocity j Corner.normalizedClusterVector)) = 0
  rw [packReal_inner,Corner.normalized_velocity_mean,Complex.ofReal_zero]

theorem resolventState_perp (j : Fin 3) : inner ℂ topState (resolventState j) = 0 := by
  change inner ℂ (packReal Corner.normalizedClusterVector) (packReal (resolventCube j)) = 0
  rw [packReal_inner,resolventCube_perp,Complex.ofReal_zero]

theorem packReal_sub (u v : Corner.ClusterField) : packReal (u-v) = packReal u - packReal v := by
  have hr : realCube (u-v) = realCube u - realCube v := by
    funext s j
    exact Complex.ofReal_sub _ _
  change pack (realCube (u-v)) = _
  rw [hr]
  exact map_sub packLinear (realCube u) (realCube v)

theorem resolventState_solves (j : Fin 3) :
    (Corner.lambdaStar : ℂ) • resolventState j - finiteK (resolventState j) = velocityState j := by
  apply Subtype.ext
  change (Corner.lambdaStar : ℂ) • (resolventState j).val - (finiteK (resolventState j)).val = _
  rw [finiteK_apply]
  change (Corner.lambdaStar : ℂ) • packReal (resolventCube j) -
    clusterPotential (packReal (resolventCube j)) = packReal (Corner.velocity j Corner.normalizedClusterVector)
  rw [clusterPotential_packReal,← packReal_smul,← packReal_sub,resolventCube_solves]

def highVelocity (j : Fin 3) : RankOneBand.highSpace topState :=
  ⟨velocityState j,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (velocityState_perp j)⟩

def highResolvent (j : Fin 3) : RankOneBand.highSpace topState :=
  ⟨resolventState j,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (resolventState_perp j)⟩

theorem baseHigh_resolvent (j : Fin 3) :
    RankOneBand.baseHigh finiteK topState Corner.lambdaStar (highResolvent j) = highVelocity j := by
  change RankOneBand.project topState
    ((Corner.lambdaStar : ℂ) • resolventState j - finiteK (resolventState j)) = highVelocity j
  rw [resolventState_solves]
  exact RankOneBand.project_embed (highVelocity j)

/-- The explicit vector is the action of the genuine bounded inverse. -/
theorem baseInverse_velocity (j : Fin 3) :
    actualCornerData.baseInverse (highVelocity j) = highResolvent j := by
  rw [← baseHigh_resolvent j]
  exact CoerciveInverse.inverse_apply _ _ _ _

theorem velocity_resolvent_inner (j k : Fin 3) :
    inner ℂ (velocityState j) (resolventState k) =
      if j = k then (Corner.hessianCoefficient j : ℂ) else 0 := by
  change inner ℂ (packReal (Corner.velocity j Corner.normalizedClusterVector))
    (packReal (resolventCube k)) = _
  rw [packReal_inner,velocity_resolvent_gram]
  by_cases h : j = k <;> simp [h]

/-- The actual inverse has exactly the certified diagonal Rayleigh coefficients. -/
theorem baseInverse_velocity_gram (j k : Fin 3) :
    inner ℂ (highVelocity j) (actualCornerData.baseInverse (highVelocity k)) =
      if j = k then (Corner.hessianCoefficient j : ℂ) else 0 := by
  rw [baseInverse_velocity]
  exact velocity_resolvent_inner j k

theorem finiteVelocity_topState (t : Momentum) :
    finiteVelocity t topState = ∑ j : Fin 3, ((Real.pi : ℂ) * t j) • velocityState j := by
  apply Subtype.ext
  change clusterProjection (clusterVelocity t topState.val) = _
  rw [clusterProjection_clusterVelocity]
  change clusterVelocity t (packReal Corner.normalizedClusterVector) = _
  rw [clusterVelocity_packReal t _ normalizedCorner_transverse]
  simp only [Submodule.coe_sum,SetLike.val_smul]
  rfl

/-- The three actual quadratic coefficients obey the paper's ellipticity bounds. -/
theorem baseInverse_velocity_diagonal_bounds (j : Fin 3) :
    (1 / 14 : ℝ) ≤ (inner ℂ (highVelocity j) (actualCornerData.baseInverse (highVelocity j))).re ∧
      (inner ℂ (highVelocity j) (actualCornerData.baseInverse (highVelocity j))).re ≤ 20 := by
  simp only [baseInverse_velocity_gram,ite_true,Complex.ofReal_re]
  exact Corner.hessianCoefficient_bounds j

end Maxwell.Continuum.CornerBridge
