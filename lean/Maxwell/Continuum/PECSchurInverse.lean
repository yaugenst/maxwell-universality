import Maxwell.Continuum.PECBlockElimination
import Maxwell.Continuum.SelfAdjointRightInverse

/-! Bounded inverse transfer through the actual PEC gradient elimination. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace SelfAdjointResolvent

@[simp] theorem gradientProjection_gradient (Ω : Opens Space) (g : gradientSpace Ω) :
    gradientProjection Ω g = g :=
  (gradientSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self g

@[simp] theorem transverseProjection_transverse (Ω : Opens Space) (t : transverseSpace Ω) :
    transverseProjection Ω t = t :=
  (transverseSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self t

@[simp] theorem gradientProjection_transverse (Ω : Opens Space) (t : transverseSpace Ω) :
    gradientProjection Ω t = 0 :=
  (gradientSpace Ω).orthogonalProjectionOnto_eq_zero_iff.mpr t.property

@[simp] theorem transverseProjection_gradient (Ω : Opens Space) (g : gradientSpace Ω) :
    transverseProjection Ω g = 0 :=
  (gradientSpace Ω).orthogonalProjectionOnto_orthogonal_apply_eq_zero g.property

/-- Reassemble the two literal orthogonal components in physical L². -/
def kernelAssemble (Ω : Opens Space) (g : gradientSpace Ω) (t : transverseSpace Ω) :
    testL2Closure Ω := (g : testL2Closure Ω) + (t : testL2Closure Ω)

@[simp] theorem gradientProjection_assemble (Ω : Opens Space)
    (g : gradientSpace Ω) (t : transverseSpace Ω) :
    gradientProjection Ω (kernelAssemble Ω g t) = g := by
  exact ((gradientProjection Ω).map_add g.val t.val).trans
    ((congrArg₂ HAdd.hAdd (gradientProjection_gradient Ω g)
      (gradientProjection_transverse Ω t)).trans (add_zero g))

@[simp] theorem transverseProjection_assemble (Ω : Opens Space)
    (g : gradientSpace Ω) (t : transverseSpace Ω) :
    transverseProjection Ω (kernelAssemble Ω g t) = t := by
  exact ((transverseProjection Ω).map_add g.val t.val).trans
    ((congrArg₂ HAdd.hAdd (transverseProjection_gradient Ω g)
      (transverseProjection_transverse Ω t)).trans (zero_add t))

theorem kernelAssemble_mem_domain (Ω : Opens Space) (g : gradientSpace Ω)
    (t : (transverseCurlCurl Ω).domain) :
    kernelAssemble Ω g t ∈ (pecCurlCurl Ω).domain :=
  (pecCurlCurl Ω).domain.add_mem (gradient_mem_domain Ω g) t.property

def kernelAssembleDomain (Ω : Opens Space) (g : gradientSpace Ω)
    (t : (transverseCurlCurl Ω).domain) : (pecCurlCurl Ω).domain :=
  ⟨kernelAssemble Ω g t, kernelAssemble_mem_domain Ω g t⟩

@[simp] theorem domainTransverseProjection_assemble (Ω : Opens Space)
    (g : gradientSpace Ω) (t : (transverseCurlCurl Ω).domain) :
    domainTransverseProjection Ω (kernelAssembleDomain Ω g t) = t :=
  Subtype.ext (transverseProjection_assemble Ω g t)

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)
variable (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)

def schurSource : testL2Closure Ω →L[ℂ] transverseSpace Ω :=
  transverseProjection Ω - (ε.materialReverseCoupling Ω).comp
    ((ε.gradientResolvent Ω ell hell).comp (gradientProjection Ω))

@[simp] theorem schurSource_apply (f : testL2Closure Ω) :
    ε.schurSource Ω ell hell f = transverseProjection Ω f -
      ε.materialReverseCoupling Ω (ε.gradientResolvent Ω ell hell (gradientProjection Ω f)) := rfl

variable (Z : BoundedInverse (ε.schurOperator Ω ell hell))

def recoveredTransverse : testL2Closure Ω →L[ℂ] transverseSpace Ω :=
  Z.map.comp (ε.schurSource Ω ell hell)

def recoveredGradient : testL2Closure Ω →L[ℂ] gradientSpace Ω :=
  -(ε.gradientResolvent Ω ell hell).comp
    (gradientProjection Ω + (ε.materialCoupling Ω).comp (ε.recoveredTransverse Ω ell hell Z))

def schurReconstruction : testL2Closure Ω →L[ℂ] testL2Closure Ω :=
  (gradientSpace Ω).subtypeL.comp (ε.recoveredGradient Ω ell hell Z) +
    (transverseSpace Ω).subtypeL.comp (ε.recoveredTransverse Ω ell hell Z)

@[simp] theorem schurReconstruction_apply (f : testL2Closure Ω) :
    ε.schurReconstruction Ω ell hell Z f =
      kernelAssemble Ω (ε.recoveredGradient Ω ell hell Z f)
        (ε.recoveredTransverse Ω ell hell Z f) := rfl

def schurReconstructionDomain (f : testL2Closure Ω) : (pecCurlCurl Ω).domain :=
  kernelAssembleDomain Ω (ε.recoveredGradient Ω ell hell Z f)
    ⟨ε.recoveredTransverse Ω ell hell Z f, Z.mem_domain (ε.schurSource Ω ell hell f)⟩

theorem shiftMaxwell_schurReconstruction (f : testL2Closure Ω) :
    shift (maxwellOperator Ω ε) ell (ε.schurReconstructionDomain Ω ell hell Z f) = f := by
  apply (ε.maxwell_equation_iff_schur Ω ell hell _ f).mpr
  have hg := gradientProjection_assemble Ω (ε.recoveredGradient Ω ell hell Z f)
    (ε.recoveredTransverse Ω ell hell Z f)
  have ht := transverseProjection_assemble Ω (ε.recoveredGradient Ω ell hell Z f)
    (ε.recoveredTransverse Ω ell hell Z f)
  constructor
  · change gradientProjection Ω (kernelAssemble Ω _ _) = _
    calc
      _ = ε.recoveredGradient Ω ell hell Z f := hg
      _ = -ε.gradientResolvent Ω ell hell
          (gradientProjection Ω f + ε.materialCoupling Ω (ε.recoveredTransverse Ω ell hell Z f)) := rfl
      _ = _ := congrArg (fun t : transverseSpace Ω =>
        -ε.gradientResolvent Ω ell hell (gradientProjection Ω f + ε.materialCoupling Ω t)) ht.symm
  · have hd := domainTransverseProjection_assemble Ω (ε.recoveredGradient Ω ell hell Z f)
      (⟨ε.recoveredTransverse Ω ell hell Z f,
        Z.mem_domain (ε.schurSource Ω ell hell f)⟩ : (transverseCurlCurl Ω).domain)
    exact (congrArg (ε.schurOperator Ω ell hell).toFun hd).trans
      (Z.apply_map (ε.schurSource Ω ell hell f))

theorem schurReconstruction_shiftMaxwell (u : (pecCurlCurl Ω).domain) :
    ε.schurReconstruction Ω ell hell Z (shift (maxwellOperator Ω ε) ell u) =
      (u : testL2Closure Ω) := by
  let f := shift (maxwellOperator Ω ε) ell u
  have he := (ε.maxwell_equation_iff_schur Ω ell hell u f).mp rfl
  have ht : ε.recoveredTransverse Ω ell hell Z f = transverseProjection Ω u := by
    calc
      _ = Z.map (ε.schurSource Ω ell hell f) := rfl
      _ = Z.map (ε.schurOperator Ω ell hell (domainTransverseProjection Ω u)) :=
        congrArg Z.map he.2.symm
      _ = _ := Z.map_apply (domainTransverseProjection Ω u)
  have hg : ε.recoveredGradient Ω ell hell Z f = gradientProjection Ω u := by
    calc
      _ = -ε.gradientResolvent Ω ell hell
          (gradientProjection Ω f + ε.materialCoupling Ω (ε.recoveredTransverse Ω ell hell Z f)) := rfl
      _ = -ε.gradientResolvent Ω ell hell
          (gradientProjection Ω f + ε.materialCoupling Ω (transverseProjection Ω u)) :=
        congrArg (fun t : transverseSpace Ω =>
          -ε.gradientResolvent Ω ell hell (gradientProjection Ω f + ε.materialCoupling Ω t)) ht
      _ = _ := he.1.symm
  exact (congrArg₂ (kernelAssemble Ω) hg ht).trans (kernel_decomposition Ω u)

/-- A genuine transverse inverse yields a genuine inverse on all physical L²,
with both laws and the actual Maxwell domain. -/
def inverseOfSchur : BoundedInverse (shift (maxwellOperator Ω ε) ell) where
  map := ε.schurReconstruction Ω ell hell Z
  mem_domain f := (ε.schurReconstructionDomain Ω ell hell Z f).property
  apply_map f := ε.shiftMaxwell_schurReconstruction Ω ell hell Z f
  map_apply u := ε.schurReconstruction_shiftMaxwell Ω ell hell Z u

@[simp] theorem schurSource_transverse (t : transverseSpace Ω) :
    ε.schurSource Ω ell hell t = t := by
  change transverseProjection Ω t -
    ε.materialReverseCoupling Ω (ε.gradientResolvent Ω ell hell (gradientProjection Ω t)) = t
  have hz : ε.materialReverseCoupling Ω
      (ε.gradientResolvent Ω ell hell (gradientProjection Ω t)) = 0 :=
    (congrArg (fun g : gradientSpace Ω =>
      ε.materialReverseCoupling Ω (ε.gradientResolvent Ω ell hell g))
        (gradientProjection_transverse Ω t)).trans
      ((congrArg (ε.materialReverseCoupling Ω) (map_zero (ε.gradientResolvent Ω ell hell))).trans
        (map_zero (ε.materialReverseCoupling Ω)))
  exact (congrArg₂ HSub.hSub (transverseProjection_transverse Ω t) hz).trans (sub_zero t)

variable (R : BoundedInverse (shift (maxwellOperator Ω ε) ell))

def inverseTransverse : transverseSpace Ω →L[ℂ] transverseSpace Ω :=
  (transverseProjection Ω).comp (R.map.comp (transverseSpace Ω).subtypeL)

def inverseTransverseDomain (f : transverseSpace Ω) : (transverseCurlCurl Ω).domain :=
  domainTransverseProjection Ω ⟨R.map f, R.mem_domain f⟩

theorem schur_inverseTransverse (f : transverseSpace Ω) :
    ε.schurOperator Ω ell hell (ε.inverseTransverseDomain Ω ell R f) = f := by
  have he := (ε.maxwell_equation_iff_schur Ω ell hell
    ⟨R.map f, R.mem_domain f⟩ (f : testL2Closure Ω)).mp (R.apply_map f)
  exact he.2.trans (ε.schurSource_transverse Ω ell hell f)

/-- Conversely, the transverse compression of the physical inverse inverts
the Schur operator, whose self-adjointness supplies the second inverse law. -/
def schurInverseOfMaxwell : BoundedInverse (ε.schurOperator Ω ell hell) :=
  BoundedInverse.ofRightInverse (ε.schurOperator Ω ell hell)
    (ε.schurOperator_selfAdjoint Ω ell hell) (ε.inverseTransverse Ω ell R)
    (fun f => (ε.inverseTransverseDomain Ω ell R f).property)
    (ε.schur_inverseTransverse Ω ell hell R)

theorem schur_boundedInverse_iff :
    Nonempty (BoundedInverse (shift (maxwellOperator Ω ε) ell)) ↔
      Nonempty (BoundedInverse (ε.schurOperator Ω ell hell)) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨ε.schurInverseOfMaxwell Ω ell hell R⟩
  · rintro ⟨Z⟩
    exact ⟨ε.inverseOfSchur Ω ell hell Z⟩

theorem mem_realSpectrum_iff_schur :
    ell ∈ realSpectrum (maxwellOperator Ω ε) ↔
      ¬Nonempty (BoundedInverse (ε.schurOperator Ω ell hell)) :=
  not_congr (ε.schur_boundedInverse_iff Ω ell hell)

end ScalarDielectric

end Maxwell.Continuum
