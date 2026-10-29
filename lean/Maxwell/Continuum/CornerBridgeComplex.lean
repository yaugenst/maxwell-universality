import Maxwell.Continuum.CornerBridgeTop

/-! Complexification of the finite real corner inside the actual alias space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement PeriodicPerturbation
open scoped InnerProductSpace

def coordinates (u : clusterSpace) : Cube := fun s j => u.val (cubeAlias s) j

theorem pack_coordinates (u : clusterSpace) : pack (coordinates u) = u.val := by
  apply eq_of_aliases
  · exact pack_noncentral _
  · exact clusterSpace_noncentral u
  · intro s
    rw [pack_alias]
    rfl

theorem coordinates_transverse (u : clusterSpace) :
    cubeProjection (coordinates u) = coordinates u := by
  apply pack_injective
  rw [← clusterProjection_pack,pack_coordinates]
  exact (mem_clusterSpace_iff _).mp u.property

def realPart (u : Cube) : Corner.ClusterField := fun s j => (u s j).re
def imagPart (u : Cube) : Corner.ClusterField := fun s j => (u s j).im

theorem cube_re_im (u : Cube) : u = realCube (realPart u) + Complex.I • realCube (imagPart u) := by
  funext s j
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,realCube,realPart,imagPart,realMomentum,mul_comm]
    using (Complex.re_add_im (u s j)).symm

theorem pack_re_im (u : Cube) :
    pack u = packReal (realPart u) + Complex.I • packReal (imagPart u) := by
  conv_lhs => rw [cube_re_im u]
  rw [pack_add,pack_smul]
  rfl

theorem realPart_projection (u : Cube) :
    realPart (cubeProjection u) = Corner.clusterProjection (realPart u) := by
  funext s i
  change (∑ j, (Corner.waveProjection s i j : ℂ) * u s j).re =
    ∑ j, Corner.waveProjection s i j * (u s j).re
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem imagPart_projection (u : Cube) :
    imagPart (cubeProjection u) = Corner.clusterProjection (imagPart u) := by
  funext s i
  change (∑ j, (Corner.waveProjection s i j : ℂ) * u s j).im =
    ∑ j, Corner.waveProjection s i j * (u s j).im
  simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

theorem coordinates_realPart_transverse (u : clusterSpace) :
    Corner.clusterProjection (realPart (coordinates u)) = realPart (coordinates u) := by
  rw [← realPart_projection,coordinates_transverse]

theorem coordinates_imagPart_transverse (u : clusterSpace) :
    Corner.clusterProjection (imagPart (coordinates u)) = imagPart (coordinates u) := by
  rw [← imagPart_projection,coordinates_transverse]

theorem mixed_real_inner (a b c d : Corner.ClusterField) :
    (inner ℂ (packReal a + Complex.I • packReal b)
      (packReal c + Complex.I • packReal d)).re =
      Corner.clusterDot a c + Corner.clusterDot b d := by
  simp [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,packReal_inner]

theorem coordinates_norm_sq (u : clusterSpace) :
    ‖u‖ ^ 2 = Corner.clusterDot (realPart (coordinates u)) (realPart (coordinates u)) +
      Corner.clusterDot (imagPart (coordinates u)) (imagPart (coordinates u)) := by
  have h := mixed_real_inner (realPart (coordinates u)) (imagPart (coordinates u))
    (realPart (coordinates u)) (imagPart (coordinates u))
  rw [← pack_re_im,pack_coordinates,inner_self_eq_norm_sq_to_K] at h
  rw [← RCLike.ofReal_pow] at h
  change ((‖u‖ ^ 2 : ℝ) : ℂ).re = _ at h
  simpa only [Complex.ofReal_re] using h

theorem coordinates_perp (u : clusterSpace) (hu : inner ℂ topState u = 0) :
    Corner.clusterDot Corner.normalizedClusterVector (realPart (coordinates u)) = 0 ∧
    Corner.clusterDot Corner.normalizedClusterVector (imagPart (coordinates u)) = 0 := by
  change inner ℂ (packReal Corner.normalizedClusterVector) u.val = 0 at hu
  rw [← pack_coordinates u,pack_re_im,inner_add_right,inner_smul_right,
    packReal_inner,packReal_inner] at hu
  constructor
  · have h := congrArg Complex.re hu
    simpa using h
  · have h := congrArg Complex.im hu
    simpa using h

theorem coordinates_K_form (u : clusterSpace) :
    (inner ℂ u (finiteK u)).re =
      Corner.clusterDot (realPart (coordinates u)) (Corner.clusterOperator (realPart (coordinates u))) +
      Corner.clusterDot (imagPart (coordinates u)) (Corner.clusterOperator (imagPart (coordinates u))) := by
  change (inner ℂ u.val (finiteK u).val).re = _
  rw [finiteK_apply,← pack_coordinates u,pack_re_im,map_add,map_smul,
    clusterPotential_packReal,clusterPotential_packReal]
  exact mixed_real_inner _ _ _ _

end Maxwell.Continuum.CornerBridge
