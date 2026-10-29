import Maxwell.Continuum.PECSchur
import Maxwell.Continuum.BlockSchur
import Maxwell.Continuum.SelfAdjointResolventData

/-! Exact gradient elimination for the actual continuum Maxwell equation. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace SelfAdjointResolvent

theorem kernel_projections_eq_iff (Ω : Opens Space) (u v : testL2Closure Ω) :
    u = v ↔ gradientProjection Ω u = gradientProjection Ω v ∧
      transverseProjection Ω u = transverseProjection Ω v := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hg, ht⟩
    calc
      u = (gradientProjection Ω u : testL2Closure Ω) +
          (transverseProjection Ω u : testL2Closure Ω) := (kernel_decomposition Ω u).symm
      _ = (gradientProjection Ω v : testL2Closure Ω) +
          (transverseProjection Ω v : testL2Closure Ω) := by rw [hg, ht]
      _ = v := kernel_decomposition Ω v

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)

/-- The reverse material block on the actual supported L² decomposition. -/
def materialReverseCoupling : gradientSpace Ω →L[ℂ] transverseSpace Ω :=
  (transverseProjection Ω).comp ((ε.domainMultiplier Ω).comp (gradientSpace Ω).subtypeL)

theorem materialReverseCoupling_eq_adjoint :
    ε.materialReverseCoupling Ω =
      ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := transverseSpace Ω) (F := gradientSpace Ω)
        (ε.materialCoupling Ω) := by
  apply ContinuousLinearMap.ext
  intro g
  exact (ε.materialCoupling_adjoint Ω g).symm

theorem shiftMaxwell_apply (ell : ℝ) (u : (pecCurlCurl Ω).domain) :
    shift (maxwellOperator Ω ε) ell u =
      pecCurlCurl Ω u - ε.domainMultiplier Ω u - (ell : ℂ) • (u : testL2Closure Ω) :=
  (SelfAdjointResolvent.shift_apply (𝕜 := ℂ) (H := testL2Closure Ω)
    (maxwellOperator Ω ε) ell u).trans
      (congrArg (fun v : testL2Closure Ω => v - (ell : ℂ) • (u : testL2Closure Ω))
        (maxwellOperator_apply Ω ε u))

theorem gradient_shiftMaxwell (ell : ℝ) (u : (pecCurlCurl Ω).domain) :
    gradientProjection Ω (shift (maxwellOperator Ω ε) ell u) =
      -GradientSchur.shift (ε.gradientMaterial Ω) ell (gradientProjection Ω u) -
        ε.materialCoupling Ω (transverseProjection Ω u) := by
  exact (congrArg (gradientProjection Ω) (ε.shiftMaxwell_apply Ω ell u)).trans
    (BlockSchur.projected_negative (gradientProjection Ω)
      (pecCurlCurl Ω u) (ε.domainMultiplier Ω u) u
      (ε.gradientMaterial Ω (gradientProjection Ω u))
      (ε.materialCoupling Ω (transverseProjection Ω u)) (ell : ℂ)
      (gradientProjection_curlCurl Ω u) (ε.gradient_material_blocks Ω u))

theorem transverse_shiftMaxwell (ell : ℝ) (u : (pecCurlCurl Ω).domain) :
    transverseProjection Ω (shift (maxwellOperator Ω ε) ell u) =
      (transverseCurlCurl Ω (domainTransverseProjection Ω u) -
        ε.transverseMaterial Ω (transverseProjection Ω u) -
        (ell : ℂ) • transverseProjection Ω u) -
          ε.materialReverseCoupling Ω (gradientProjection Ω u) := by
  have hc : transverseProjection Ω (pecCurlCurl Ω u) =
      transverseCurlCurl Ω (domainTransverseProjection Ω u) := by
    apply Subtype.ext
    have hp := (transverseSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨pecCurlCurl Ω u, pecCurlCurl_mem_transverse Ω u⟩ : transverseSpace Ω)
    exact (congrArg Subtype.val hp).trans (transverseCurlCurl_projection Ω u).symm
  have hm : transverseProjection Ω (ε.domainMultiplier Ω u) =
      ε.materialReverseCoupling Ω (gradientProjection Ω u) +
        ε.transverseMaterial Ω (transverseProjection Ω u) :=
    (ε.transverse_material_blocks Ω u).trans
      (congrArg (fun v : transverseSpace Ω => v + ε.transverseMaterial Ω (transverseProjection Ω u))
        (ε.materialCoupling_adjoint Ω (gradientProjection Ω u)))
  exact (congrArg (transverseProjection Ω) (ε.shiftMaxwell_apply Ω ell u)).trans
    (BlockSchur.projected_transverse (transverseProjection Ω)
      (pecCurlCurl Ω u) (ε.domainMultiplier Ω u) u
      (transverseCurlCurl Ω (domainTransverseProjection Ω u))
      (ε.materialReverseCoupling Ω (gradientProjection Ω u))
      (ε.transverseMaterial Ω (transverseProjection Ω u)) (ell : ℂ) hc hm)

theorem schurOperator_blocks (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (t : (transverseCurlCurl Ω).domain) :
    ε.schurOperator Ω ell hell t =
      (transverseCurlCurl Ω t - ε.transverseMaterial Ω t - (ell : ℂ) • (t : transverseSpace Ω)) +
        ε.materialReverseCoupling Ω (ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω t)) := by
  let z := ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω t)
  let F := ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := transverseSpace Ω) (F := gradientSpace Ω)
    (ε.materialCoupling Ω)
  have hF : F z = ε.materialReverseCoupling Ω z := ε.materialCoupling_adjoint Ω z
  calc
    _ = transverseCurlCurl Ω t +
        (-ε.transverseMaterial Ω t - (ell : ℂ) • (t : transverseSpace Ω) + F z) := rfl
    _ = (transverseCurlCurl Ω t - ε.transverseMaterial Ω t -
        (ell : ℂ) • (t : transverseSpace Ω)) + F z := by abel
    _ = _ := congrArg (fun v : transverseSpace Ω =>
      (transverseCurlCurl Ω t - ε.transverseMaterial Ω t -
        (ell : ℂ) • (t : transverseSpace Ω)) + v) hF

/-- Both the source correction and the reconstructed gradient component are
derived from the literal Maxwell equation on D(C). -/
theorem maxwell_equation_iff_schur (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (u : (pecCurlCurl Ω).domain) (f : testL2Closure Ω) :
    shift (maxwellOperator Ω ε) ell u = f ↔
      (gradientProjection Ω u =
        -ε.gradientResolvent Ω ell hell
          (gradientProjection Ω f + ε.materialCoupling Ω (transverseProjection Ω u)) ∧
       ε.schurOperator Ω ell hell (domainTransverseProjection Ω u) =
        transverseProjection Ω f -
          ε.materialReverseCoupling Ω (ε.gradientResolvent Ω ell hell (gradientProjection Ω f))) := by
  have h := BlockSchur.negativeBlock_elimination (G := gradientSpace Ω) (T := transverseSpace Ω)
    (GradientSchur.shift (G := gradientSpace Ω) (ε.gradientMaterial Ω) ell)
    (ε.gradientResolvent Ω ell hell)
    (ε.materialCoupling Ω) (ε.materialReverseCoupling Ω)
    (fun x => ε.gradientResolvent_left Ω ell hell x)
    (fun x => ε.gradientResolvent_right Ω ell hell x)
    (gradientProjection Ω u) (transverseProjection Ω u)
    (transverseCurlCurl Ω (domainTransverseProjection Ω u) -
      ε.transverseMaterial Ω (transverseProjection Ω u) - (ell : ℂ) • transverseProjection Ω u)
    (gradientProjection Ω f) (transverseProjection Ω f)
  have hg := ε.gradient_shiftMaxwell Ω ell u
  have ht := ε.transverse_shiftMaxwell Ω ell u
  have hs := ε.schurOperator_blocks Ω ell hell (domainTransverseProjection Ω u)
  constructor
  · intro heq
    have hp := (kernel_projections_eq_iff Ω _ f).mp heq
    have hb := h.mp ⟨hg.symm.trans hp.1, ht.symm.trans hp.2⟩
    exact ⟨hb.1, hs.trans hb.2⟩
  · intro heq
    have hb := h.mpr ⟨heq.1, hs.symm.trans heq.2⟩
    exact (kernel_projections_eq_iff Ω _ f).mpr ⟨hg.trans hb.1, ht.trans hb.2⟩

end ScalarDielectric

end Maxwell.Continuum
