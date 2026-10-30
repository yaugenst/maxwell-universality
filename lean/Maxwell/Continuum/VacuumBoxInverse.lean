import Maxwell.Continuum.VacuumBoxGap
import Maxwell.Continuum.SelfAdjointResolventMaxwell

/-! A genuine bounded inverse on the full physical unit PEC cube with
constant dielectric one, including its infinite curl-free subspace. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.VacuumBox

open MeasureTheory SelfAdjointResolvent

def material : ScalarDielectric where
  coefficient _ := 1
  measurable := measurable_const
  lower _ := le_rfl
  upper _ := by norm_num

@[simp] theorem material_scalarProduct (u : ScalarL2) : material.scalarProduct u = u := by
  apply Lp.ext
  filter_upwards [material.scalarProduct_ae u] with x hx
  simpa only [material,Complex.ofReal_one,one_mul] using hx

@[simp] theorem material_multiplier (u : FieldL2) : material.multiplier u = u := by
  apply PiLp.ext
  intro i
  exact material_scalarProduct (u i)

@[simp] theorem material_domainMultiplier (Ω : TopologicalSpace.Opens Space)
    (u : testL2Closure Ω) : material.domainMultiplier Ω u = u :=
  Subtype.ext (material_multiplier u.val)

@[simp] theorem maxwell_apply (u : (maxwellOperator domain material).domain) :
    maxwellOperator domain material u = pecCurlCurl domain u-(u : testL2Closure domain) := by
  rw [maxwellOperator_apply,material_domainMultiplier]

theorem transverse_shift_norm (u : (transverseCurlCurl domain).domain) :
    ‖(u : transverseSpace domain)‖ ≤
      ‖transverseCurlCurl domain u-(u : transverseSpace domain)‖ := by
  have he := transverse_shift_energy u
  have hi := re_inner_le_norm (𝕜 := ℂ) (u : transverseSpace domain)
    (transverseCurlCurl domain u-(u : transverseSpace domain))
  change (inner ℂ (u : transverseSpace domain)
    (transverseCurlCurl domain u-(u : transverseSpace domain))).re ≤
      ‖(u : transverseSpace domain)‖*‖transverseCurlCurl domain u-(u : transverseSpace domain)‖ at hi
  by_cases hz : (u : transverseSpace domain) = 0
  · rw [hz,norm_zero]
    exact norm_nonneg _
  · have hp := norm_pos_iff.mpr hz
    nlinarith only [he,hi,hp]

theorem gradient_maxwell (u : (maxwellOperator domain material).domain) :
    gradientProjection domain (maxwellOperator domain material u) =
      -gradientProjection domain (u : testL2Closure domain) := by
  rw [maxwell_apply,map_sub,gradientProjection_curlCurl,zero_sub]

theorem transverse_maxwell (u : (maxwellOperator domain material).domain) :
    transverseProjection domain (maxwellOperator domain material u) =
      transverseCurlCurl domain (domainTransverseProjection domain u)-
        transverseProjection domain (u : testL2Closure domain) := by
  rw [maxwell_apply,map_sub]
  congr 1
  apply Subtype.ext
  have hp := (transverseSpace domain).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨pecCurlCurl domain u,pecCurlCurl_mem_transverse domain u⟩ : transverseSpace domain)
  exact (congrArg Subtype.val hp).trans (transverseCurlCurl_projection domain u).symm

theorem lower_norm (u : (maxwellOperator domain material).domain) :
    ‖(u : testL2Closure domain)‖ ≤ ‖maxwellOperator domain material u‖ := by
  have hx := (gradientSpace domain).norm_sq_eq_add_norm_sq_projection
    (u : testL2Closure domain)
  have hy := (gradientSpace domain).norm_sq_eq_add_norm_sq_projection
    (maxwellOperator domain material u)
  change ‖(u : testL2Closure domain)‖^2 =
    ‖gradientProjection domain u‖^2+‖transverseProjection domain u‖^2 at hx
  change ‖maxwellOperator domain material u‖^2 =
    ‖gradientProjection domain (maxwellOperator domain material u)‖^2+
    ‖transverseProjection domain (maxwellOperator domain material u)‖^2 at hy
  rw [gradient_maxwell,transverse_maxwell,norm_neg] at hy
  have ht := transverse_shift_norm (domainTransverseProjection domain u)
  change ‖transverseProjection domain u‖ ≤
    ‖transverseCurlCurl domain (domainTransverseProjection domain u)-
      transverseProjection domain u‖ at ht
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ht
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [hx,hy,hs])

def inverse : BoundedInverse (maxwellOperator domain material) :=
  BoundedInverse.ofLowerBound (maxwellOperator_selfAdjoint domain material)
    (by norm_num : (0 : ℝ)<1) (fun u => by simpa only [one_mul] using lower_norm u)

theorem inverse_norm : ‖inverse.map‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have h := lower_norm ⟨inverse.map f,inverse.mem_domain f⟩
  simpa only [inverse.apply_map,one_mul] using h

theorem inverse_graph_bounds :
    ‖maxwellGraphInverse domain material inverse‖ ≤ 27 ∧
      ‖maxwellGraphMap domain material‖*‖maxwellGraphInverse domain material inverse‖ ≤ 702 := by
  simpa only [mul_one] using
    maxwell_inverse_graph_bounds domain material inverse (le_refl (1 : ℝ)) inverse_norm

#print axioms lower_norm
#print axioms inverse_norm
#print axioms inverse_graph_bounds

end Maxwell.Continuum.VacuumBox
