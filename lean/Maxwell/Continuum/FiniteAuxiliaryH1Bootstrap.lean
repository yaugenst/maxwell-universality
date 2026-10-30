import Maxwell.Continuum.FiniteAuxiliaryWellTranslation
import Maxwell.Continuum.FiniteAuxiliaryH1Algebra
import Maxwell.Continuum.BoundaryCellH1

/-! Actual H¹ regularity of the solved finite-well source, obtained from
its exact translated source equation and the genuine Fourier difference
quotient construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FourierSobolev

open Bloch Filter MeasureTheory
open scoped Topology

private theorem component_axis_bound (f : FieldL2) {M : ℝ}
    (hb : ∀ j t, ‖fieldTranslation (t • coordinateDirection j) f-f‖ ≤ M*|t|)
    (j k : Fin 3) : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) (f k)-f k‖ ≤ M*|t| := by
  apply Eventually.of_forall
  intro t
  exact (PiLp.norm_apply_le (fieldTranslation (t • coordinateDirection j) f-f) k).trans (hb j t)

def h1OfAxisBounds (f : FieldL2) {M : ℝ}
    (hb : ∀ j t, ‖fieldTranslation (t • coordinateDirection j) f-f‖ ≤ M*|t|) : H1Data f where
  derivative j := WithLp.toLp 2 fun k => weakDerivative j (f k) (component_axis_bound f hb j k)
  weak_derivative j k := weakDerivative_distribution j (f k) (component_axis_bound f hb j k)

theorem h1OfAxisBounds_norm (f : FieldL2) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j t, ‖fieldTranslation (t • coordinateDirection j) f-f‖ ≤ M*|t|) :
    (h1OfAxisBounds f hb).norm ≤ ‖f‖+3*M := by
  have hd (j : Fin 3) : ‖(h1OfAxisBounds f hb).derivative j‖^2 ≤ 3*M^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin 3, M^2 := Finset.sum_le_sum fun k _ =>
        (sq_le_sq₀ (norm_nonneg _) hM).mpr
          (weakDerivative_norm_le j (f k) hM (component_axis_bound f hb j k))
      _ = _ := by simp
  have hg : ∑ j : Fin 3, ‖(h1OfAxisBounds f hb).derivative j‖^2 ≤ 9*M^2 := by
    calc
      _ ≤ ∑ _ : Fin 3, 3*M^2 := Finset.sum_le_sum fun j _ => hd j
      _ = _ := by simp; ring
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith only [hg, mul_nonneg (norm_nonneg f) hM]⟩

end Maxwell.Continuum.FourierSobolev

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch FourierSobolev

attribute [local irreducible] Auxiliary.resolvent Qh

variable {ι : Type*} [Fintype ι]

theorem auxiliarySource_translation_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) (a : Space) :
    sourceEquation D hσ0 hσ r v
      (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-auxiliarySource D hσ0 hσ r A f) =
    fieldTranslation a f-f+
      wellTranslationCommutator h r v a (auxiliaryField D hσ0 hσ r A f)+
      finiteWellOperator h r v
        (resolventTranslationCommutator D hσ0 hσ a (auxiliarySource D hσ0 hσ r A f)) := by
  have he := congrArg (fun u => fieldTranslation a u)
    (auxiliarySource_equation D hσ0 hσ r v hv A hA f)
  rw [map_add] at he
  have hu : auxiliarySource D hσ0 hσ r A f-
      finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f) = f := by
    rw [auxiliarySource_equation D hσ0 hσ r v hv A hA f, add_sub_cancel_right]
  have ht : fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-
      fieldTranslation a (finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f)) =
      fieldTranslation a f := by rw [he, add_sub_cancel_right]
  change fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-auxiliarySource D hσ0 hσ r A f-
    finiteWellOperator h r v (resolvent D hσ0 hσ
      (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-auxiliarySource D hσ0 hσ r A f)) = _
  change _ = fieldTranslation a f-f+
    (fieldTranslation a (finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f))-
      finiteWellOperator h r v (fieldTranslation a (auxiliaryField D hσ0 hσ r A f)))+
    finiteWellOperator h r v
      (fieldTranslation a (auxiliaryField D hσ0 hσ r A f)-
        resolvent D hσ0 hσ (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)))
  calc
    _ = (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-
          fieldTranslation a (finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f)))-
        (auxiliarySource D hσ0 hσ r A f-finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f))+
        (fieldTranslation a (finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f))-
          finiteWellOperator h r v (resolvent D hσ0 hσ
            (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)))) := by
      rw [map_sub, map_sub]
      dsimp only [auxiliaryField]
      abel
    _ = _ := by
      rw [hu, ht, map_sub]
      abel

def sourceTranslationBound {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) {f : FieldL2} (Df : H1Data f) (V : ℝ) : ℝ :=
  ‖sourceInverse D hσ0 hσ r A‖ *
    (Df.norm+(800*V*h*(4*(h^2)⁻¹)+V*448*(h^4)⁻¹)*‖auxiliarySource D hσ0 hσ r A f‖)

theorem sourceTranslationBound_nonneg {h z σ V : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) {f : FieldL2} (Df : H1Data f) (hV : 0 ≤ V) :
    0 ≤ sourceTranslationBound D hσ0 hσ r A Df V := by
  unfold sourceTranslationBound
  have hh := D.h_pos
  have hn := CellGauge.h1_norm_nonneg Df
  positivity

theorem auxiliarySource_axis_bound {h z σ V : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hV : 0 ≤ V) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    {f : FieldL2} (Df : H1Data f) (j : Fin 3) (t : ℝ) :
    ‖fieldTranslation (t • coordinateDirection j) (auxiliarySource D hσ0 hσ r A f)-
      auxiliarySource D hσ0 hσ r A f‖ ≤ sourceTranslationBound D hσ0 hσ r A Df V*|t| := by
  have hp := D.h_pos
  let a := t • coordinateDirection j
  have hn : ‖a‖ = |t| := coordinate_shift_norm j t
  have hleft := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 =>
    T (fieldTranslation a (auxiliarySource D hσ0 hσ r A f)-auxiliarySource D hσ0 hσ r A f))
      (sourceInverse_left D hσ0 hσ r v (fun i => (hv0 i).ne') A hA)
  simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at hleft
  rw [auxiliarySource_translation_identity D hσ0 hσ r v (fun i => (hv0 i).ne') A hA] at hleft
  have hdf := (Df.coordinate_translation_bound j t).trans
    (mul_le_mul_of_nonneg_right (CellGauge.h1_derivative_norm_le Df j) (abs_nonneg t))
  have hw := (wellTranslationCommutator h r v a).le_of_opNorm_le
    (wellTranslationCommutator_norm D.h_pos hV r v (fun i => (hv0 i).le) hv hdisj a)
    (auxiliaryField D hσ0 hσ r A f)
  have hr := (resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le D hσ0 hσ)
    (auxiliarySource D hσ0 hσ r A f)
  change ‖auxiliaryField D hσ0 hσ r A f‖ ≤ _ at hr
  have hwr := (finiteWellOperator h r v).le_of_opNorm_le
    (finiteWellOperator_norm_le D.h_pos hV r v (fun i => (hv0 i).le) hv hdisj)
    (resolventTranslationCommutator D hσ0 hσ a (auxiliarySource D hσ0 hσ r A f))
  have hrc := (resolventTranslationCommutator D hσ0 hσ a).le_of_opNorm_le
    (resolventTranslationCommutator_norm_le D hσ0 hσ a)
    (auxiliarySource D hσ0 hσ r A f)
  rw [hn] at hw hrc
  rw [← hleft]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hadd := norm_add_le
    (fieldTranslation a f-f+wellTranslationCommutator h r v a (auxiliaryField D hσ0 hσ r A f))
    (finiteWellOperator h r v (resolventTranslationCommutator D hσ0 hσ a
      (auxiliarySource D hσ0 hσ r A f)))
  have hadd' := norm_add_le (fieldTranslation a f-f)
    (wellTranslationCommutator h r v a (auxiliaryField D hσ0 hσ r A f))
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hr (by positivity))
  have hwr' := hwr.trans (mul_le_mul_of_nonneg_left hrc hV)
  change _ ≤ sourceTranslationBound D hσ0 hσ r A Df V*|t|
  unfold sourceTranslationBound
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ Df.norm*|t|+(800*V*h*|t|)*((4*(h^2)⁻¹)*‖auxiliarySource D hσ0 hσ r A f‖)+
        V*((448*(h^4)⁻¹*|t|)*‖auxiliarySource D hσ0 hσ r A f‖) := by
      linarith only [hadd, hadd', hdf, hw', hwr']
    _ = _ := by ring

def auxiliarySourceH1 {h z σ V : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hV : 0 ≤ V) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    {f : FieldL2} (Df : H1Data f) : H1Data (auxiliarySource D hσ0 hσ r A f) :=
  h1OfAxisBounds _ (auxiliarySource_axis_bound D hσ0 hσ r v hv0 hV hv hdisj A hA Df)

#print axioms auxiliarySourceH1

end Maxwell.Continuum.FiniteAuxiliary
