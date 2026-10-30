import Maxwell.Continuum.FiniteAuxiliarySourceEncoding

/-! The finite source representation itself is supported in the actual
buffered PEC box. No derivatives or point evaluation of its output
are required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory Maxwell.Composition BoxCutoff CellGauge SchwartzMultiplier

variable {ι : Type*} [Fintype ι]

theorem templateSynthesis_supported (a : ι → FieldL2) (g : BrightSpace ι)
    (s : ι → Set Space)
    (ha : ∀ i k, ∀ᵐ x ∂volume, x ∉ s i → a i k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, x ∉ s i) → templateSynthesis a g k x = 0 := by
  have he : templateSynthesis a g k = ∑ i, g i • a i k := by
    rw [templateSynthesis_apply]
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  rw [he]
  have hi : ∀ i, ∀ᵐ x ∂volume, x ∉ s i → (g i • a i k) x = 0 := by
    intro i
    filter_upwards [ha i k, Lp.coeFn_smul (g i) (a i k)] with x hx hc hn
    rw [hc, Pi.smul_apply, hx hn, smul_zero]
  filter_upwards [ae_all_iff.mpr hi, Lp.coeFn_finsetSum Finset.univ (fun i => g i • a i k)]
    with x hx hs hn
  rw [hs, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hx i (hn i))

variable (S : Source.SparseSystem) (precision : ℕ)

theorem emittedSource_supported (P : ℕ) (ĉ : ℚ)
    (r : SourceDecoration.Vertex S precision → Space) (L : ℝ)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i k, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → a i k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, L ≤ ‖x-r i‖) → emittedSource S precision P ĉ a k x = 0 := by
  have he := templateSynthesis_supported
    (fun i => a (sourceInputSite S precision i)) (dyadicSourceVector S P ĉ)
    (fun i => Metric.ball (r (sourceInputSite S precision i)) L)
    (fun i => ha (sourceInputSite S precision i)) k
  filter_upwards [he] with x hx hn
  apply hx
  intro i
  simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hn (sourceInputSite S precision i)

theorem emittedSource_interior (P : ℕ) (ĉ : ℚ)
    (n : Fin 3 → ℕ) {L b : ℝ} (hb : 0 ≤ b)
    (r : SourceDecoration.Vertex S precision → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i k, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → a i k x = 0) :
    familyProjection (interiorCells n b) (emittedSource S precision P ĉ a) =
      emittedSource S precision P ĉ a :=
  well_support_interior n hb r hr _ (emittedSource_supported S precision P ĉ r L a ha)

theorem emittedSource_mem_PEC (P : ℕ) (ĉ : ℚ)
    (n : Fin 3 → ℕ) {L b : ℝ} (hb : 0 ≤ b)
    (r : SourceDecoration.Vertex S precision → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i k, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → a i k x = 0) :
    emittedSource S precision P ĉ a ∈ testL2Closure (BoxModes.boxDomain (side n)) := by
  have he := cutoff_preserves_source n hb _ (emittedSource_interior S precision P ĉ n hb r hr a ha)
  have hf := (cutoffPhysicalField (BoxModes.boxDomain (side n))
    (schwartz (side n)) (schwartz_interior (side n)) (emittedSource S precision P ĉ a)).property
  change field (schwartz (side n)) (emittedSource S precision P ĉ a) ∈ _ at hf
  rwa [he] at hf

#print axioms emittedSource_supported
#print axioms emittedSource_mem_PEC

end Maxwell.Continuum.FiniteAuxiliary
