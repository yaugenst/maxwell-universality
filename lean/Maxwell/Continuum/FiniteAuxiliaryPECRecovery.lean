import Maxwell.Continuum.FiniteAuxiliaryBoxResidual
import Maxwell.Continuum.FiniteAuxiliaryReadoutCutoff
import Maxwell.Continuum.SelfAdjointResolventMaxwell

/-! Every-domain-field recovery for the actual PEC Maxwell operator.
The only approximation inputs are explicit source, material and
observable errors; the field estimate uses its genuine sampled inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants Bloch CellGauge BoxCutoff
open TopologicalSpace SelfAdjointResolvent

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs
attribute [local irreducible] pecCurlCurl

def referenceGraph {h z σ : ℝ} (D : Calibration h z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) : OperatorDomain (BoxModes.boxDomain N) :=
  ⟨WithLp.toLp 2 (referenceField D hσ0 hσ N f,
      pecCurlCurl (BoxModes.boxDomain N) (referenceDomain D hσ0 hσ N Df)),
    (pecCurlCurl (BoxModes.boxDomain N)).mem_graph_iff.mpr
      ⟨referenceDomain D hσ0 hσ N Df, rfl, rfl⟩⟩

theorem referenceGraph_inclusion {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) :
    GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain N)) (referenceGraph D hσ0 hσ N Df) =
      referenceField D hσ0 hσ N f := rfl

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inverse_graph_difference (C : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (R : BoundedInverse (FormPerturbation.addBounded C (-B)))
    {K : ℝ} (hR : ‖R.map‖ ≤ K) (u v : GraphNorm.space C) :
    ‖GraphNorm.inclusion C u-GraphNorm.inclusion C v‖ ≤
      K*‖GraphNorm.perturbed C B u-GraphNorm.perturbed C B v‖ := by
  have he := R.perturbed_residual_bound C B hR u (GraphNorm.perturbed C B v)
  have hi := congrArg (GraphNorm.inclusion C) (R.perturbed_inverse_apply C B v)
  rw [R.inclusion_perturbedGraphInverse C B] at hi
  rw [hi] at he
  exact he

end Abstract

theorem graph_field_difference (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {K : ℝ} (hR : ‖R.map‖ ≤ K)
    (u v : OperatorDomain Ω) :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u-GraphNorm.inclusion (pecCurlCurl Ω) v‖ ≤
      K*‖maxwellGraphMap Ω ε u-maxwellGraphMap Ω ε v‖ := by
  exact inverse_graph_difference (pecCurlCurl Ω) (ε.domainMultiplier Ω) R hR u v

theorem every_field_three_errors (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {K η δf δr δm : ℝ} (hR : ‖R.map‖ ≤ K)
    (u v : OperatorDomain Ω) (f : testL2Closure Ω) (fideal : FieldL2)
    (B : FieldL2 →L[ℂ] FieldL2)
    (hu : ‖maxwellGraphMap Ω ε u-f‖ ≤ η)
    (hf : ‖(f : FieldL2)-fideal‖ ≤ δf)
    (hr : ‖(GraphNorm.action (pecCurlCurl Ω) v : FieldL2)-
      B (GraphNorm.inclusion (pecCurlCurl Ω) v)-fideal‖ ≤ δr)
    (hm : ‖ε.multiplier-B‖ ≤ δm) :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u-GraphNorm.inclusion (pecCurlCurl Ω) v‖ ≤
      K*(η+δf+δr+δm*‖GraphNorm.inclusion (pecCurlCurl Ω) v‖) := by
  have hK : 0 ≤ K := (norm_nonneg R.map).trans hR
  apply (graph_field_difference Ω ε R hR u v).trans
  apply mul_le_mul_of_nonneg_left _ hK
  have he : ((maxwellGraphMap Ω ε u : testL2Closure Ω) : FieldL2)-
      ((maxwellGraphMap Ω ε v : testL2Closure Ω) : FieldL2) =
      (((maxwellGraphMap Ω ε u : testL2Closure Ω) : FieldL2)-(f : FieldL2))+
        ((f : FieldL2)-fideal)-
        ((GraphNorm.action (pecCurlCurl Ω) v : FieldL2)-
          B (GraphNorm.inclusion (pecCurlCurl Ω) v)-fideal)+
        (ε.multiplier-B) (GraphNorm.inclusion (pecCurlCurl Ω) v) := by
    change _-((GraphNorm.action (pecCurlCurl Ω) v : FieldL2)-
      ε.multiplier (GraphNorm.inclusion (pecCurlCurl Ω) v)) = _
    simp only [sub_apply]
    abel
  change ‖((maxwellGraphMap Ω ε u : testL2Closure Ω) : FieldL2)-
    ((maxwellGraphMap Ω ε v : testL2Closure Ω) : FieldL2)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hu hf)) hr))
    ((ε.multiplier-B).le_of_opNorm_le hm _))

variable {ι : Type*} [Fintype ι]

def assembledMaterial (h E : ℝ) (r : ι → Space) (v : ι → ℝ) : FieldL2 →L[ℂ] FieldL2 :=
  PeriodicMaterial.dielectric.multiplier+(E : ℂ) • ContinuousLinearMap.id ℂ FieldL2+
    finiteWellOperator h r v

theorem referenceGraph_residual {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ)
    (r : ι → Space) (v : ι → ℝ) {f : FieldL2} (Df : H1Data f) (g : FieldL2) :
    (GraphNorm.action (pecCurlCurl (BoxModes.boxDomain N)) (referenceGraph D hσ0 hσ N Df) : FieldL2)-
      assembledMaterial h (z+σ) r v
        (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain N)) (referenceGraph D hσ0 hσ N Df))-g =
      referenceResidual D hσ0 hσ N r v Df g := by
  rw [referenceGraph_inclusion]
  change (pecCurlCurl (BoxModes.boxDomain N) (referenceDomain D hσ0 hσ N Df) : FieldL2)-
    assembledMaterial h (z+σ) r v (referenceField D hσ0 hσ N f)-g = _
  simp only [assembledMaterial, add_apply, smul_apply, ContinuousLinearMap.id_apply, referenceResidual]
  abel

theorem finite_observable_error {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (O Oideal : FieldL2 →L[ℂ] H) {δ V e : ℝ}
    (hO : ‖O-Oideal‖ ≤ δ) (hV : ‖Oideal‖ ≤ V) (u uref : FieldL2)
    (he : ‖u-uref‖ ≤ e) : ‖O u-Oideal uref‖ ≤ δ*‖uref‖+(δ+V)*e := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans hO
  have hv : 0 ≤ V := (norm_nonneg _).trans hV
  have hu : ‖u‖ ≤ ‖uref‖+e := by
    have ht := norm_add_le uref (u-uref)
    rw [add_sub_cancel] at ht
    exact ht.trans (add_le_add le_rfl he)
  have hi : O u-Oideal uref = (O-Oideal) u+Oideal (u-uref) := by
    simp only [sub_apply, map_sub]
    abel
  rw [hi]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ δ*(‖uref‖+e)+V*e := add_le_add
      (((O-Oideal).le_of_opNorm_le hO u).trans (mul_le_mul_of_nonneg_left hu hd))
      ((Oideal.le_of_opNorm_le hV _).trans (mul_le_mul_of_nonneg_left he hv))
    _ = _ := by ring

#print axioms every_field_three_errors
#print axioms referenceGraph_residual
#print axioms finite_observable_error

end Maxwell.Continuum.FiniteAuxiliary
