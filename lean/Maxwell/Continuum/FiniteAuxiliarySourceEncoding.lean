import Maxwell.Continuum.FiniteAuxiliarySourceAmplitudes
import Maxwell.Continuum.FiniteAuxiliaryRecoveryTolerance
import Maxwell.Continuum.FiniteAuxiliaryReadoutCutoff

/-! Actual n-term dyadic source output. Its L² error follows from the
finite template certificate, shared rational scalar enclosure, and
the explicit dyadic working precision. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition Maxwell.Logical MeasureTheory EffectiveMass Auxiliary MasterConstants

variable {ι : Type*} [Fintype ι]

theorem templateSynthesis_single [DecidableEq ι] (a : ι → FieldL2) (i : ι) (c : ℂ) :
    templateSynthesis a (PiLp.single 2 i c) = c • a i := by
  rw [templateSynthesis_apply]
  simp only [PiLp.single_apply, ite_smul, zero_smul]
  simpa only [Finset.mem_univ, ite_true] using
    Finset.sum_ite_eq' Finset.univ i (fun j => c • a j)

theorem field_difference_supported (a b : FieldL2) (s : Set Space)
    (ha : ∀ k, ∀ᵐ x ∂volume, x ∉ s → a k x = 0)
    (hb : ∀ k, ∀ᵐ x ∂volume, x ∉ s → b k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂volume, x ∉ s → (a-b) k x = 0 := by
  filter_upwards [ha k, hb k, Lp.coeFn_sub (a k) (b k)] with x hx hy he hnot
  change (a k-b k) x = 0
  rw [he, Pi.sub_apply, hx hnot, hy hnot, sub_self]

theorem idealSource_scale_le_one {L z α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    |α/muH D (inverse_length_le_1024 hL)| ≤ 1 := by
  have hμ := muH_pos D (inverse_length_le_1024 hL)
  have hi : (muH D (inverse_length_le_1024 hL))⁻¹ ≤ 1 := by
    apply (muH_inverse_le D (inverse_length_le_1024 hL)).trans
    apply (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^128 ≤ 2^130)
      (sq_nonneg L⁻¹)).trans
    exact readout_strength_budget hL
  rw [abs_of_nonneg (div_nonneg hα hμ.le), div_eq_mul_inv]
  exact (mul_le_mul hα1 hi (inv_nonneg.mpr hμ.le) zero_le_one).trans_eq (one_mul 1)

variable (S : Source.SparseSystem) (precision : ℕ)

theorem templateSynthesis_routed (a : SourceDecoration.Vertex S precision → FieldL2) :
    templateSynthesis a (routedForcing S precision) =
      templateSynthesis (fun i => a (sourceInputSite S precision i)) (originalComplexSource S) := by
  classical
  let : DecidableEq (SourceDecoration.Vertex S precision) := sourceAmplitudeSiteDecidableEq S precision
  rw [routedForcing_sum_original, map_sum, templateSynthesis_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact templateSynthesis_single a (sourceInputSite S precision i) _

def emittedSource (P : ℕ) (ĉ : ℚ) (a : SourceDecoration.Vertex S precision → FieldL2) : FieldL2 :=
  templateSynthesis (fun i => a (sourceInputSite S precision i)) (dyadicSourceVector S P ĉ)

theorem emittedSource_sum (P : ℕ) (ĉ : ℚ) (a : SourceDecoration.Vertex S precision → FieldL2) :
    emittedSource S precision P ĉ a = ∑ i : Fin S.n,
      (((sourceAmplitude S P ĉ i).value : ℝ) : ℂ) • a (sourceInputSite S precision i) := by
  rw [emittedSource, templateSynthesis_apply]
  rfl

theorem emittedSource_error (hunit : IsUnit (Source.realMatrix S)) (hb : S.source ≠ 0)
    {L z α e : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (r : SourceDecoration.Vertex S precision → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i, ‖a i‖ ≤ 2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → a i k x = 0)
    (he : 0 ≤ e)
    (hab : ∀ i, ‖a i-siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL))‖ ≤ e/4)
    (P : ℕ) (ĉ : ℚ)
    (hĉ : |(ĉ : ℝ)-α/muH D (inverse_length_le_1024 hL)| ≤ e/16)
    (hP : (S.nnz : ℝ)*(1/2 : ℝ)^P ≤ e/16) :
    ‖emittedSource S precision P ĉ a-
      idealSource D (inverse_length_le_1024 hL) r α (routedForcing S precision)‖ ≤
      e*‖routedForcing S precision‖ := by
  let p := sourceInputSite S precision
  let b := fun i => siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL))
  have hdisj' : Pairwise fun i j => Disjoint (Metric.ball (r (p i)) L) (Metric.ball (r (p j)) L) :=
    fun i j hij => hdisj ((sourceInputSite_injective S precision).ne hij)
  have hb' (i : SourceDecoration.Vertex S precision) (k : Fin 3) :
      ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → b i k x = 0 := by
    rw [show b i = Bloch.fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL)) from rfl]
    apply translated_supported_ball
    intro j
    simpa only [inv_inv] using actualSource_supported D (inverse_length_le_1024 hL) j
  have hA : ‖templateSynthesis (fun i => a (p i))‖ ≤ 2 :=
    templateSynthesis_norm (by norm_num) _ (fun i => ha (p i))
      (fun i j hij => field_inner_eq_zero_of_disjoint (hdisj' hij) (hsa (p i)) (hsa (p j)))
  have hAB : ‖templateSynthesis (fun i => a (p i))-templateSynthesis (fun i => b (p i))‖ ≤ e/4 :=
    templateSynthesis_error (by positivity) _ _ (fun i => hab (p i))
      (fun i => Metric.ball (r (p i)) L) hdisj'
      (fun i => field_difference_supported _ _ _ (hsa (p i)) (hb' (p i)))
  have hround : ‖dyadicSourceVector S P ĉ-(ĉ : ℂ) • originalComplexSource S‖ ≤
      e*‖originalComplexSource S‖/16 := by
    apply (dyadicSourceVector_error S P ĉ).trans
    have hn : (S.n : ℝ) ≤ S.nnz := by exact_mod_cast Source.dimension_le_nnz S hunit
    have hsmall := (mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (1/2 : ℝ)^P)).trans hP
    have hg : 1 ≤ ‖originalComplexSource S‖ := by
      rw [originalComplexSource_norm S precision]
      exact (routedForcing_norm_bounds S hb precision).1
    nlinarith only [hsmall, mul_le_mul_of_nonneg_left hg he]
  have hout := templateSource_error_budget (fun i => a (p i)) (fun i => b (p i)) he hA hAB
    (idealSource_scale_le_one hL D hα hα1) hĉ (originalComplexSource S) (dyadicSourceVector S P ĉ) hround
  rw [originalComplexSource_norm S precision] at hout
  rw [idealSource_templateSynthesis, templateSynthesis_routed]
  exact hout

#print axioms emittedSource_error

end Maxwell.Continuum.FiniteAuxiliary
