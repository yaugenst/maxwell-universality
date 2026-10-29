import Maxwell.Continuum.PECSchurInverse
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The physical Maxwell and transverse Schur kernels are linearly
equivalent, so gradient elimination preserves the exact multiplicity. -/

noncomputable section

namespace Maxwell.Continuum.ScalarDielectric

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace SelfAdjointResolvent

variable (ε : ScalarDielectric) (Ω : Opens Space)
variable (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)

theorem maxwell_kernel_equation_iff (u : (pecCurlCurl Ω).domain) :
    shift (maxwellOperator Ω ε) ell u = 0 ↔
      gradientProjection Ω u = -ε.gradientResolvent Ω ell hell
        (ε.materialCoupling Ω (transverseProjection Ω u)) ∧
      ε.schurOperator Ω ell hell (domainTransverseProjection Ω u) = 0 := by
  simpa only [map_zero, zero_add, sub_zero] using
    ε.maxwell_equation_iff_schur Ω ell hell u 0

def maxwellKernelDomain : (shift (maxwellOperator Ω ε) ell).ker →ₗ[ℂ] (pecCurlCurl Ω).domain :=
  Submodule.inclusion (shift (maxwellOperator Ω ε) ell).ker_le_domain

theorem maxwellKernelDomain_eq_zero (u : (shift (maxwellOperator Ω ε) ell).ker) :
    shift (maxwellOperator Ω ε) ell (ε.maxwellKernelDomain Ω ell u) = 0 :=
  LinearPMap.coe_mem_ker_iff.mp u.property

def schurKernelDomain : (ε.schurOperator Ω ell hell).ker →ₗ[ℂ] (transverseCurlCurl Ω).domain :=
  Submodule.inclusion (ε.schurOperator Ω ell hell).ker_le_domain

def kernelTransverse : (shift (maxwellOperator Ω ε) ell).ker →ₗ[ℂ]
    (ε.schurOperator Ω ell hell).ker :=
  ((transverseProjection Ω).toLinearMap.comp
    (shift (maxwellOperator Ω ε) ell).ker.subtype).codRestrict
      (ε.schurOperator Ω ell hell).ker (by
        intro u
        apply (LinearPMap.coe_mem_ker_iff (f := ε.schurOperator Ω ell hell)
          (x := domainTransverseProjection Ω (ε.maxwellKernelDomain Ω ell u))).mpr
        exact ((ε.maxwell_kernel_equation_iff Ω ell hell
          (ε.maxwellKernelDomain Ω ell u)).mp (ε.maxwellKernelDomain_eq_zero Ω ell u)).2)

def kernelGradientGraph : transverseSpace Ω →L[ℂ] testL2Closure Ω :=
  (gradientSpace Ω).subtypeL.comp
    (-(ε.gradientResolvent Ω ell hell).comp (ε.materialCoupling Ω)) +
      (transverseSpace Ω).subtypeL

theorem kernelGradientGraph_mem_domain (t : (transverseCurlCurl Ω).domain) :
    ε.kernelGradientGraph Ω ell hell t ∈ (pecCurlCurl Ω).domain :=
  kernelAssemble_mem_domain Ω (-ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω t)) t

theorem kernelGradientGraph_mem_ker (x : (ε.schurOperator Ω ell hell).ker) :
    ε.kernelGradientGraph Ω ell hell x ∈ (shift (maxwellOperator Ω ε) ell).ker := by
  let t := ε.schurKernelDomain Ω ell hell x
  let g := -ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω x)
  apply (LinearPMap.coe_mem_ker_iff (f := shift (maxwellOperator Ω ε) ell)
    (x := kernelAssembleDomain Ω g t)).mpr
  apply (ε.maxwell_kernel_equation_iff Ω ell hell _).mpr
  constructor
  · exact (gradientProjection_assemble Ω g t).trans
      (congrArg (fun z : transverseSpace Ω =>
        -ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω z))
        (transverseProjection_assemble Ω g t).symm)
  · exact (congrArg (ε.schurOperator Ω ell hell).toFun
      (domainTransverseProjection_assemble Ω g t)).trans
        (LinearPMap.coe_mem_ker_iff.mp x.property)

def kernelLift : (ε.schurOperator Ω ell hell).ker →ₗ[ℂ]
    (shift (maxwellOperator Ω ε) ell).ker :=
  ((ε.kernelGradientGraph Ω ell hell).toLinearMap.comp
    (ε.schurOperator Ω ell hell).ker.subtype).codRestrict
      (shift (maxwellOperator Ω ε) ell).ker (ε.kernelGradientGraph_mem_ker Ω ell hell)

theorem kernelTransverse_lift (x : (ε.schurOperator Ω ell hell).ker) :
    ε.kernelTransverse Ω ell hell (ε.kernelLift Ω ell hell x) = x := by
  apply Subtype.ext
  exact transverseProjection_assemble Ω
    (-ε.gradientResolvent Ω ell hell (ε.materialCoupling Ω x)) x

theorem kernelLift_transverse (u : (shift (maxwellOperator Ω ε) ell).ker) :
    ε.kernelLift Ω ell hell (ε.kernelTransverse Ω ell hell u) = u := by
  apply Subtype.ext
  have hg := ((ε.maxwell_kernel_equation_iff Ω ell hell
    (ε.maxwellKernelDomain Ω ell u)).mp (ε.maxwellKernelDomain_eq_zero Ω ell u)).1
  exact (congrArg (fun g : gradientSpace Ω =>
    kernelAssemble Ω g (transverseProjection Ω u)) hg.symm).trans (kernel_decomposition Ω u)

def schurKernelEquiv : (shift (maxwellOperator Ω ε) ell).ker ≃ₗ[ℂ]
    (ε.schurOperator Ω ell hell).ker where
  __ := ε.kernelTransverse Ω ell hell
  invFun := ε.kernelLift Ω ell hell
  left_inv := ε.kernelLift_transverse Ω ell hell
  right_inv := ε.kernelTransverse_lift Ω ell hell

theorem schur_kernel_finrank_eq :
    Module.finrank ℂ (shift (maxwellOperator Ω ε) ell).ker =
      Module.finrank ℂ (ε.schurOperator Ω ell hell).ker :=
  (ε.schurKernelEquiv Ω ell hell).finrank_eq

end Maxwell.Continuum.ScalarDielectric
