import Maxwell.Continuum.PeriodicPoleLimitContour

/-! Actual dominated convergence at the selected imaginary pole. The
full within-cell operator, Fourier phase, and fixed-order almost-analytic
cutoff occur literally in the Bochner integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic CellGauge Set Metric MeasureTheory Filter
open scoped Topology

attribute [local irreducible] poleContourIntegrand fullCellSymbol imaginaryPole

theorem poleContourIntegrand_stronglyMeasurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    StronglyMeasurable (poleContourIntegrand D hh j R s) := by
  apply ContinuousOn.stronglyMeasurable_of_countable_compl
    (s := ({0} : Set Space)ᶜ)
  · intro q hq
    exact (poleContourIntegrand_continuousAt_spatial D hh j R hs hq).continuousWithinAt
  · simpa only [compl_compl] using countable_singleton (0 : Space)

theorem poleContourIntegrand_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (poleContourIntegrand D hh j R s) volume := by
  apply poleContourMajorant_integrable.mono'
    (poleContourIntegrand_stronglyMeasurable D hh j R hs).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : Space)] with q hq
  exact poleContourIntegrand_norm_le D hh j R hphase hs hq

theorem poleContour_integral_tendsto {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R) :
    Tendsto (fun s : ℝ => ∫ q, poleContourIntegrand D hh j R s q)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ q, poleContourIntegrand D hh j R 1 q)) := by
  rw [← nhdsWithin_Ico_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
  apply tendsto_integral_filter_of_dominated_convergence poleContourMajorant
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (poleContourIntegrand_stronglyMeasurable D hh j R ⟨hs.1, hs.2.le⟩).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [volume.ae_ne (0 : Space)] with q hq
    exact poleContourIntegrand_norm_le D hh j R hphase ⟨hs.1, hs.2.le⟩ hq
  · exact poleContourMajorant_integrable
  · filter_upwards [volume.ae_ne (0 : Space)] with q hq
    exact (poleContourIntegrand_continuousAt_parameter D hh j R
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hq).continuousWithinAt

theorem poleContour_integral_norm_difference_tendsto {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R) :
    Tendsto (fun s : ℝ => ∫ q, ‖poleContourIntegrand D hh j R s q -
      poleContourIntegrand D hh j R 1 q‖) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  rw [← nhdsWithin_Ico_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hc := poleContourIntegrand_stronglyMeasurable D hh j R h1
  have ht : Tendsto (fun s : ℝ => ∫ q, ‖poleContourIntegrand D hh j R s q -
      poleContourIntegrand D hh j R 1 q‖) (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (∫ _q : Space, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun q => 2*poleContourMajorant q)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((poleContourIntegrand_stronglyMeasurable D hh j R ⟨hs.1, hs.2.le⟩).sub hc).norm.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [volume.ae_ne (0 : Space)] with q hq
      rw [norm_norm]
      exact (norm_sub_le _ _).trans ((add_le_add
        (poleContourIntegrand_norm_le D hh j R hphase ⟨hs.1, hs.2.le⟩ hq)
        (poleContourIntegrand_norm_le D hh j R hphase h1 hq)).trans_eq (by ring))
    · exact poleContourMajorant_integrable.const_mul 2
    · filter_upwards [volume.ae_ne (0 : Space)] with q hq
      have hp : Tendsto (fun t : ℝ => poleContourIntegrand D hh j R t q)
          (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (poleContourIntegrand D hh j R 1 q)) :=
        (poleContourIntegrand_continuousAt_parameter D hh j R h1 hq).continuousWithinAt
      simpa only [sub_self, norm_zero] using
        (hp.sub_const (poleContourIntegrand D hh j R 1 q)).norm
  simpa only [integral_zero] using ht

theorem poleContour_initial_integral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space) :
    (∫ q, poleContourIntegrand D hh j R 0 q) = OperatorFourier.angularFourier
      (fun q => (Well.chi smallRadius q : ℂ) • fullCellSymbol z 0 (realMomentumMap q)) (-R) := by
  unfold poleContourIntegrand
  exact initial_integral_eq _ _ _ _

end Maxwell.Continuum.PeriodicBand
