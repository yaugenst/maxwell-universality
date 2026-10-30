import Maxwell.Continuum.FiniteAuxiliarySite

/-! The finite direct sum of actual continuum well restrictions. Disjoint
well supports give a contraction independently of the number of wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary MeasureTheory

variable {ι : Type*} [Fintype ι]

abbrev DefectSpace (ι : Type*) := PiLp 2 (fun _ : ι => FieldL2)

def collection (h : ℝ) (r : ι → Space) : FieldL2 →L[ℂ] DefectSpace ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => FieldL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => siteRestriction h (r i))

omit [Fintype ι] in
@[simp] theorem collection_apply (h : ℝ) (r : ι → Space) (f : FieldL2) (i : ι) :
    collection h r f i = siteRestriction h (r i) f := rfl

def insertion (h : ℝ) (r : ι → Space) : DefectSpace ι →L[ℂ] FieldL2 :=
  ∑ i, (siteInsertion h (r i)).comp (PiLp.proj 2 (fun _ : ι => FieldL2) i)

@[simp] theorem insertion_apply (h : ℝ) (r : ι → Space) (f : DefectSpace ι) :
    insertion h r f = ∑ i, siteInsertion h (r i) (f i) := by
  simp only [insertion, sum_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]

theorem collection_adjoint (h : ℝ) (r : ι → Space) :
    (collection h r).adjoint = insertion h r := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [insertion_apply, sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← siteRestriction_adjoint, ContinuousLinearMap.adjoint_inner_left, collection_apply]

def diagonal (v : ι → ℝ) : DefectSpace ι →L[ℂ] DefectSpace ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => FieldL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (v i : ℂ) • PiLp.proj 2 (fun _ : ι => FieldL2) i)

omit [Fintype ι] in
@[simp] theorem diagonal_apply (v : ι → ℝ) (f : DefectSpace ι) (i : ι) :
    diagonal v f i = (v i : ℂ) • f i := rfl

omit [Fintype ι] in
theorem diagonal_one : diagonal (fun _ : ι => (1 : ℝ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [diagonal_apply, Complex.ofReal_one, one_smul, one_apply_eq_self]

theorem collection_weighted_square (h : ℝ) (r : ι → Space) (v : ι → ℝ) :
    (collection h r).adjoint.comp ((diagonal v).comp (collection h r)) =
      finiteWellOperator h r v := by
  rw [collection_adjoint]
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, insertion_apply, diagonal_apply,
    collection_apply, map_smul, finiteWellOperator, sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ContinuousLinearMap.comp_apply,
    siteInsertion_restriction]

theorem collection_square (h : ℝ) (r : ι → Space) :
    (collection h r).adjoint.comp (collection h r) =
      finiteWellOperator h r (fun _ => 1) := by
  simpa only [diagonal_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    collection_weighted_square h r (fun _ => 1)

theorem collection_norm {h : ℝ} (hh : 0 < h) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹)) :
    ‖collection h r‖ ≤ 1 := by
  have hb := finiteWellOperator_norm_le hh zero_le_one r (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) hdisj
  rw [← collection_square, ContinuousLinearMap.norm_adjoint_comp_self] at hb
  nlinarith only [hb, norm_nonneg (collection h r)]

theorem insertion_norm {h : ℝ} (hh : 0 < h) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹)) :
    ‖insertion h r‖ ≤ 1 := by
  rw [← collection_adjoint, LinearIsometryEquiv.norm_map]
  exact collection_norm hh r hdisj

#print axioms collection_adjoint
#print axioms collection_weighted_square
#print axioms collection_norm

end Maxwell.Continuum.FiniteAuxiliary
