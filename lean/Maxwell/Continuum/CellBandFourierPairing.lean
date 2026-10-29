import Maxwell.Continuum.CellBandFourierReality

/-! Parseval for the physical cell and the actual dual bilinear
normalization at opposite complex momenta. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization PeriodicBand MeasureTheory UnitAddTorus Set
open scoped Pointwise

theorem component_inner_integrable (u v : FiberSpace) (j : Fin 3) :
    Integrable (fun x => inner ℂ (periodicSeries u x j) (periodicSeries v x j)) torusMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (scalarCellL2 u j) (scalarCellL2 v j)).congr
  filter_upwards [scalarCellL2_ae u j, scalarCellL2_ae v j] with x hx hy
  rw [hx, hy]

theorem periodicSeries_mean_inner (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) :
    (∫ x, inner ℂ (periodicSeries u x) (periodicSeries v x) ∂torusMeasure) = inner ℂ u v := by
  simp only [PiLp.inner_apply]
  rw [integral_finsetSum Finset.univ (fun j _ => component_inner_integrable u v j)]
  have hj (j : Fin 3) :
      (∫ x, inner ℂ (periodicSeries u x j) (periodicSeries v x j) ∂torusMeasure) =
        inner ℂ (componentSequence u j) (componentSequence v j) := by
    rw [← mFourierBasis.repr.symm.inner_map_map, ← scalarCellL2_eq_fourier u hu j,
      ← scalarCellL2_eq_fourier v hv j, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarCellL2_ae u j, scalarCellL2_ae v j] with x hx hy
    rw [hx, hy]
  simp only [hj, lp.inner_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    lp.summable_inner (𝕜 := ℂ) (componentSequence u j) (componentSequence v j))]
  apply tsum_congr
  intro ν
  rfl

theorem antiperiodicField_inner (u v : FiberSpace) (x : Space) :
    inner ℂ (antiperiodicField u x) (antiperiodicField v x) =
      inner ℂ (periodicSeries u (torusPoint x)) (periodicSeries v (torusPoint x)) := by
  change inner ℂ (carrier x • periodicSeries u (torusPoint x))
    (carrier x • periodicSeries v (torusPoint x)) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', carrier_norm]
  norm_num

theorem periodicSeries_inner_integral_unitSpatialCell (u v : FiberSpace) :
    (∫ x, inner ℂ (periodicSeries u x) (periodicSeries v x) ∂torusMeasure) =
      ∫ x in unitSpatialCell, inner ℂ (antiperiodicField u ((2 : ℝ) • x))
        (antiperiodicField v ((2 : ℝ) • x)) := by
  have ht := integral_preimage (fun x : Torus => inner ℂ (periodicSeries u x) (periodicSeries v x))
    (fun _ : Fin 3 => (0 : ℝ))
  have he : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage_emb he
    {x : Fin 3 → ℝ | ∀ j, x j ∈ Ioc 0 1}
  have hi := hp.integral_comp he (fun x : Fin 3 → ℝ =>
    inner ℂ (periodicSeries u (fun j => (x j : UnitAddCircle)))
      (periodicSeries v (fun j => (x j : UnitAddCircle))))
  have hpoint (x : Space) : torusPoint ((2 : ℝ) • x) = fun j => (x j : UnitAddCircle) := by
    funext j
    change (((2 * x j) / 2 : ℝ) : UnitAddCircle) = (x j : UnitAddCircle)
    congr 1
    ring
  simp only [zero_add] at ht
  change (∫ x, inner ℂ (periodicSeries u x) (periodicSeries v x) ∂torusMeasure) = _ at ht
  rw [ht, ← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change inner ℂ (periodicSeries u (fun j => (x j : UnitAddCircle)))
      (periodicSeries v (fun j => (x j : UnitAddCircle))) =
      inner ℂ (antiperiodicField u ((2 : ℝ) • x)) (antiperiodicField v ((2 : ℝ) • x))
    rw [antiperiodicField_inner, hpoint]

theorem physical_mean_inner (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) :
    (1/8 : ℝ) • (∫ x in physicalCell, inner ℂ (antiperiodicField u x) (antiperiodicField v x)) =
      inner ℂ u v := by
  have hscale := Measure.setIntegral_comp_smul_of_pos (volume : Measure Space)
    (fun x => inner ℂ (antiperiodicField u x) (antiperiodicField v x)) unitSpatialCell
    (by norm_num : (0 : ℝ) < 2)
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  rw [hdim] at hscale
  change (∫ x in unitSpatialCell, inner ℂ (antiperiodicField u ((2 : ℝ) • x))
    (antiperiodicField v ((2 : ℝ) • x))) =
      ((2 : ℝ)^3)⁻¹ • (∫ x in physicalCell, inner ℂ (antiperiodicField u x) (antiperiodicField v x)) at hscale
  norm_num only at hscale
  rw [← periodicSeries_mean_inner u v hu hv, periodicSeries_inner_integral_unitSpatialCell, hscale]

theorem normalizedFiberVector_star_summable {t : Momentum} (ht : t ∈ chart) :
    Summable (fun ν => ‖star (normalizedFiberVector t) ν‖) := by
  simpa only [fiber_star_apply, norm_star] using (normalizedFiberVector_fourier_l1 ht).1

theorem cellEigenfunction_dual_star {t : Momentum} (ht : t ∈ chart) (x : Space) :
    star (cellEigenfunction (-t) x) =
      Complex.I • antiperiodicField (star (normalizedFiberVector t)) x := by
  rw [cellEigenfunction, star_smul,
    antiperiodicField_star _ (normalizedFiberVector_fourier_l1 (chart_neg ht)).1,
    reversal_star, normalizedFiberVector_reversal (chart_neg ht), neg_neg, star_neg,
    antiperiodicField_neg _ (normalizedFiberVector_star_summable ht)]
  simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]

theorem cellEigenfunction_dual_pairing {t : Momentum} (ht : t ∈ chart) :
    (1/8 : ℝ) • (∫ x in physicalCell, bilinear (cellEigenfunction (-t) x) (cellEigenfunction t x)) = 1 := by
  have heq (x : Space) : bilinear (cellEigenfunction (-t) x) (cellEigenfunction t x) =
      inner ℂ (antiperiodicField (star (normalizedFiberVector t)) x)
        (antiperiodicField (normalizedFiberVector t) x) := by
    rw [bilinear_apply, cellEigenfunction_dual_star ht, cellEigenfunction,
      inner_smul_left, inner_smul_right]
    simp only [Complex.conj_I]
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  simp_rw [heq]
  rw [physical_mean_inner _ _ (normalizedFiberVector_star_summable ht)
    (normalizedFiberVector_fourier_l1 ht).1]
  exact normalizedFiberVector_bilinear ht

#print axioms physical_mean_inner
#print axioms cellEigenfunction_dual_pairing

end Maxwell.Continuum.CellBandFourier
