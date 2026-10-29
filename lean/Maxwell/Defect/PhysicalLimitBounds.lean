import Maxwell.Defect.PhysicalLimit

/-! Bounds and the one-sided limit for the actual physical compression,
including its real symmetric finite-coordinate representation. -/
namespace Maxwell.Defect.PhysicalLimit

open MeasureTheory Set Filter Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.AnalyticEigenbranch
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1200000

section GeneralIntegral
variable {X F H : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The far-region bound uses pointwise actual inverses, even at an energy
where a different Bloch point is singular. -/
theorem fullResolvent_integral_difference_bound (μ : Measure X)
    (T : X → H →L[ℂ] H) (C : X → (H →L[ℂ] H) →L[ℝ] F)
    (weight : X → ℝ) (energy s t g : ℝ) (hg : 0 < g)
    (hs : Integrable (fun x => C x (T x - ((energy - s : ℝ) : ℂ) • 1).inverse) μ)
    (ht : Integrable (fun x => C x (T x - ((energy - t : ℝ) : ℂ) • 1).inverse) μ)
    (hw : Integrable weight μ)
    (hdata : ∀ᵐ x ∂μ,
      (T x - ((energy - s : ℝ) : ℂ) • 1).IsInvertible ∧
      (T x - ((energy - t : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(T x - ((energy - s : ℝ) : ℂ) • 1).inverse‖ ≤ g⁻¹ ∧
      ‖(T x - ((energy - t : ℝ) : ℂ) • 1).inverse‖ ≤ g⁻¹ ∧ ‖C x‖ ≤ weight x) :
    ‖(∫ x, C x (T x - ((energy - s : ℝ) : ℂ) • 1).inverse ∂μ) -
      ∫ x, C x (T x - ((energy - t : ℝ) : ℂ) • 1).inverse ∂μ‖ ≤
      ((∫ x, weight x ∂μ) / g ^ 2) * |s - t| := by
  have hz (x : X) (z : ℂ) : regularResolvent (T x) 0 z = (T x - z • 1).inverse := by
    simp [regularResolvent]
  have h := regularResolvent_integral_difference_bound T (fun _ => 0) C weight energy (-s) (-t) g hg
    (by simpa only [hz, Complex.ofReal_neg, ← sub_eq_add_neg, ← Complex.ofReal_sub] using hs)
    (by simpa only [hz, Complex.ofReal_neg, ← sub_eq_add_neg, ← Complex.ofReal_sub] using ht)
    hw (by
      filter_upwards [hdata] with x hx
      simpa only [hz, mul_zero, zero_mul, add_zero,
        Complex.ofReal_neg, ← sub_eq_add_neg, ← Complex.ofReal_sub, true_and] using hx)
  simpa only [hz, Complex.ofReal_neg, ← sub_eq_add_neg, ← Complex.ofReal_sub,
    neg_sub_neg, abs_sub_comm t s] using h

end GeneralIntegral

def sourceMap (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (center : Torus) (q : Momentum) :
    FiberOperator →L[ℝ] LocalOperator (N := N) :=
  (sourceCompression (localSource edges W center q)).restrictScalars ℝ

private theorem real_smul_one (r : ℝ) :
    (r : ℂ) • (1 : FiberOperator) = r • (1 : FiberOperator) :=
  algebraMap_smul ℂ r (1 : FiberOperator)

/-- Both regular contributions have a linear energy-error bound derived
from actual resolvent identities and a shared integrable source weight. -/
theorem regularPart_difference_bound (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (center : Torus) (P : Momentum → FiberOperator)
    (edge radius ξ g : ℝ) (hg : 0 < g) (hξ : 0 ≤ ξ) (weight : Momentum → ℝ)
    (hl0 : IntegrableOn (regularDensity edges W m center P edge 0) (Metric.ball 0 radius))
    (hlξ : IntegrableOn (regularDensity edges W m center P edge ξ) (Metric.ball 0 radius))
    (hf0 : IntegrableOn (fullDensity edges W m center edge)
      (TorusChart.physicalCell \ Metric.ball 0 radius))
    (hfξ : IntegrableOn (fullDensity edges W m center (edge - ξ))
      (TorusChart.physicalCell \ Metric.ball 0 radius))
    (hwl : IntegrableOn weight (Metric.ball 0 radius))
    (hwf : IntegrableOn weight (TorusChart.physicalCell \ Metric.ball 0 radius))
    (hlocal : ∀ q ∈ Metric.ball 0 radius,
      P q * P q = P q ∧ P q * fiber m center q = fiber m center q * P q ∧
      (fiber m center q - (edge : ℂ) • 1 + P q).IsInvertible ∧
      (fiber m center q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible ∧
      ‖regularResolvent (fiber m center q) (P q) edge‖ ≤ g⁻¹ ∧
      ‖regularResolvent (fiber m center q) (P q) ((edge - ξ : ℝ) : ℂ)‖ ≤ g⁻¹ ∧
      ‖sourceMap edges W center q‖ ≤ weight q)
    (hfar : ∀ q ∈ TorusChart.physicalCell \ Metric.ball 0 radius,
      (fiber m center q - (edge : ℂ) • 1).IsInvertible ∧
      (fiber m center q - ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(fiber m center q - (edge : ℂ) • 1).inverse‖ ≤ g⁻¹ ∧
      ‖(fiber m center q - ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ g⁻¹ ∧
      ‖sourceMap edges W center q‖ ≤ weight q) :
    ‖regularPart edges W m center P edge radius 0 -
      regularPart edges W m center P edge radius ξ‖ ≤
      (((∫ q in Metric.ball 0 radius, weight q) +
        ∫ q in TorusChart.physicalCell \ Metric.ball 0 radius, weight q) / g^2) * ξ := by
  have hl := regularResolvent_integral_difference_bound
    (μ := volume.restrict (Metric.ball (0 : Momentum) radius))
    (fiber m center) P (sourceMap edges W center) weight edge 0 (-ξ) g hg
    (hl0.congr (Eventually.of_forall fun q => by
      simp [regularDensity, sourceMap]))
    (hlξ.congr (Eventually.of_forall fun q => by
      simp [regularDensity, sourceMap, sub_eq_add_neg]))
    hwl (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
      simpa only [Complex.ofReal_zero, add_zero, ← Complex.ofReal_neg,
        ← Complex.ofReal_add, ← sub_eq_add_neg] using hlocal q hq)
  have hf := fullResolvent_integral_difference_bound
    (volume.restrict (TorusChart.physicalCell \ Metric.ball (0 : Momentum) radius))
    (fiber m center) (sourceMap edges W center) weight edge 0 ξ g hg
    (hf0.congr (Eventually.of_forall fun q => by
      simp [fullDensity, sourceMap, real_smul_one]))
    (hfξ.congr (Eventually.of_forall fun q => by
      simp [fullDensity, sourceMap]))
    hwf (by
      filter_upwards [ae_restrict_mem (TorusChart.measurableSet_physicalCell.diff measurableSet_ball)] with q hq
      simpa only [sub_zero] using hfar q hq)
  simp only [zero_sub, neg_neg, abs_neg, abs_of_nonneg hξ] at hl hf
  have he : regularPart edges W m center P edge radius 0 -
      regularPart edges W m center P edge radius ξ =
      ((∫ q in Metric.ball 0 radius, regularDensity edges W m center P edge 0 q) -
        ∫ q in Metric.ball 0 radius, regularDensity edges W m center P edge ξ q) +
      ((∫ q in TorusChart.physicalCell \ Metric.ball 0 radius, fullDensity edges W m center edge q) -
        ∫ q in TorusChart.physicalCell \ Metric.ball 0 radius, fullDensity edges W m center (edge - ξ) q) := by
    simp only [regularPart, sub_zero]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hh := add_le_add hl hf
  convert hh using 1
  · simp [regularDensity, fullDensity, sourceMap, sub_eq_add_neg, real_smul_one]
  · ring

/-- Exact norm continuity follows from the proved square-root remainder;
it does not posit any infinite-lattice inverse at the limiting energy. -/
theorem tendsto_of_sqrt_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : ℝ → F) (S₀ B : F) (c K r : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (h : ∀ ξ, 0 < ξ → ξ < r → ‖S₀ - S ξ - (c * Real.sqrt ξ) • B‖ ≤ K * ξ) :
    Tendsto S (𝓝[>] 0) (𝓝 S₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcont : Continuous (fun ξ : ℝ => c * Real.sqrt ξ * ‖B‖ + K * ξ) := by fun_prop
  have hlim : Tendsto (fun ξ : ℝ => c * Real.sqrt ξ * ‖B‖ + K * ξ) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  have hs : ∀ᶠ ξ : ℝ in 𝓝[>] 0, ξ < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hs] with ξ hξ hξr
  have ht := norm_le_norm_add_norm_sub ((c * Real.sqrt ξ) • B) (S₀ - S ξ)
  rw [norm_sub_rev ((c * Real.sqrt ξ) • B) (S₀ - S ξ), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (Real.sqrt_nonneg ξ))] at ht
  rw [norm_sub_rev]
  linarith [h ξ hξ hξr]

/-- Apply the established local chart expansion to the actual compression
decomposition. The constant is explicit in the regular integral bound. -/
theorem physical_sqrt_expansion (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (edge ξ L : ℝ)
    (C : LocalBandChart (LocalOperator (N := N))) (hξ : 0 < ξ)
    (hdecomp : compression edges W m K hK hm (edge - ξ) =
      (1 / (2 * Real.pi)^3 : ℝ) •
        (C.localPart ξ + regularPart edges W m center P edge C.radius ξ))
    (hreg : ‖regularPart edges W m center P edge C.radius 0 -
      regularPart edges W m center P edge C.radius ξ‖ ≤ L * ξ) :
    ‖edgeLimit edges W m center P edge C - compression edges W m K hK hm (edge - ξ) -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator‖ ≤
        ((C.localRemainder + L) / (2 * Real.pi)^3) * ξ := by
  rw [hdecomp]
  exact C.sqrt_expansion (regularPart edges W m center P edge C.radius) hξ hreg

theorem compression_tendsto_edge (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (edge L r : ℝ) (hr : 0 < r)
    (C : LocalBandChart (LocalOperator (N := N)))
    (hdecomp : ∀ ξ, 0 < ξ → ξ < r → compression edges W m K hK hm (edge - ξ) =
      (1 / (2 * Real.pi)^3 : ℝ) •
        (C.localPart ξ + regularPart edges W m center P edge C.radius ξ))
    (hreg : ∀ ξ, 0 < ξ → ξ < r → ‖regularPart edges W m center P edge C.radius 0 -
      regularPart edges W m center P edge C.radius ξ‖ ≤ L * ξ) :
    Tendsto (fun ξ => compression edges W m K hK hm (edge - ξ)) (𝓝[>] 0)
      (𝓝 (edgeLimit edges W m center P edge C)) := by
  apply tendsto_of_sqrt_bound _ _ C.edgeNumerator C.edgeCoefficient
    ((C.localRemainder + L) / (2 * Real.pi)^3) r C.edgeCoefficient_pos.le hr
  intro ξ hξ hξr
  exact physical_sqrt_expansion edges W m K hK hm center P edge ξ L C hξ
    (hdecomp ξ hξ hξr) (hreg ξ hξ hξr)

theorem compression_selfAdjoint (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (E : ℝ) :
    IsSelfAdjoint (compression edges W m K hK hm E) := by
  apply sourceCompression_selfAdjoint
  apply IsSelfAdjoint.ringInverse
  apply (electricOperator_selfAdjoint (periodicCoefficient m) K hK hm).sub
  exact (show IsSelfAdjoint (E : ℂ) by simp [IsSelfAdjoint]).smul (by simp [IsSelfAdjoint])

/-- Norm convergence preserves the self-adjoint symmetry of the actual
compression; the real limit therefore has the exact symmetry used by the
finite-dimensional rank-one branch construction. -/
theorem edgeLimit_selfAdjoint (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (edge : ℝ)
    (C : LocalBandChart (LocalOperator (N := N)))
    (hlim : Tendsto (fun ξ => compression edges W m K hK hm (edge - ξ)) (𝓝[>] 0)
      (𝓝 (edgeLimit edges W m center P edge C))) :
    IsSelfAdjoint (edgeLimit edges W m center P edge C) := by
  have hs := ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hlim
  have hs' : Tendsto (fun ξ => compression edges W m K hK hm (edge - ξ)) (𝓝[>] 0)
      (𝓝 (ContinuousLinearMap.adjoint (edgeLimit edges W m center P edge C))) :=
    hs.congr' (Eventually.of_forall fun ξ => by
    change (compression edges W m K hK hm (edge - ξ)).adjoint = _
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (compression_selfAdjoint edges W m K hK hm (edge - ξ)).star_eq)
  change star (edgeLimit edges W m center P edge C) = _
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact tendsto_nhds_unique hs' hlim

theorem edgeLimit_real_symmetric (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (edge : ℝ)
    (C : LocalBandChart (LocalOperator (N := N)))
    (hlim : Tendsto (fun ξ => compression edges W m K hK hm (edge - ξ)) (𝓝[>] 0)
      (𝓝 (edgeLimit edges W m center P edge C))) :
    (realPartOperator (edgeLimit edges W m center P edge C)).toLinearMap.IsSymmetric :=
  realPartOperator_symmetric _ (edgeLimit_selfAdjoint edges W m K hK hm center P edge C hlim)

/-- The same error estimate passes to the actual real-coordinate operator
and the real coherent source, with no norm loss or independent limit. -/
theorem real_physical_sqrt_expansion (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (center : Torus) (P : Momentum → FiberOperator) (edge ξ L : ℝ)
    (C : LocalBandChart (LocalOperator (N := N))) (w : EuclideanSpace ℝ (Fin N))
    (hw : C.edgeNumerator = InnerProductSpace.rankOne ℂ
      (realCoordinateEmbedding w) (realCoordinateEmbedding w))
    (h : ‖edgeLimit edges W m center P edge C - compression edges W m K hK hm (edge - ξ) -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator‖ ≤ L * ξ) :
    ‖realPartOperator (edgeLimit edges W m center P edge C) -
      realPartOperator (compression edges W m K hK hm (edge - ξ)) -
      (C.edgeCoefficient * Real.sqrt ξ) • InnerProductSpace.rankOne ℝ w w‖ ≤ L * ξ := by
  have hb := (realPartOperator_norm_le
    (edgeLimit edges W m center P edge C - compression edges W m K hK hm (edge - ξ) -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator)).trans h
  have hn : realPartOperator C.edgeNumerator = InnerProductSpace.rankOne ℝ w w := by
    rw [hw, realPartOperator_rankOne]
  change ‖realPartOperatorMap
    (edgeLimit edges W m center P edge C - compression edges W m K hK hm (edge - ξ) -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator)‖ ≤ L * ξ at hb
  simpa only [map_sub, map_smul, realPartOperatorMap_apply, hn] using hb

end
end Maxwell.Defect.PhysicalLimit
