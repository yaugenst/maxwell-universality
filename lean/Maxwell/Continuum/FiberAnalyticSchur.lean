import Maxwell.Continuum.FiberAnalyticPolynomial

/-!
# Total holomorphic Schur formula

The correction is a total operator-valued function of complex momentum and
energy. On the certified box it is exactly the compression of the actual
infinite Maxwell complement inverse. Its finite restriction is obtained
by a fixed continuous linear compression map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement

abbrev ClusterMap := clusterSpace →L[ℂ] clusterSpace

def schurCorrectionExtension (z : Parameter) : FiberMap :=
  directQuadratic z.1 -
    ((backgroundAmplitude : ℂ)⁻¹ • leftCouplingExtension z) * complementInverseExtension z *
      ((backgroundAmplitude : ℂ)⁻¹ • rightCouplingExtension z)

def effectiveSchurExtension (z : Parameter) : FiberMap :=
  leadingCluster z.1 z.2 + (backgroundAmplitude : ℂ) • schurCorrectionExtension z

theorem schurCorrectionExtension_eq (z : Parameter) (hz : InBox z) :
    schurCorrectionExtension z = schurCorrection z.1 z.2 hz.1 hz.2 := by
  rw [schurCorrectionExtension, leftCouplingExtension_eq z hz.1,
    rightCouplingExtension_eq z hz.1, complementInverseExtension_eq z hz]
  rfl

theorem effectiveSchurExtension_eq (z : Parameter) (hz : InBox z) :
    effectiveSchurExtension z = effectiveSchur z.1 z.2 hz.1 hz.2 := by
  rw [effectiveSchurExtension, schurCorrectionExtension_eq z hz]
  rfl

theorem analyticAt_schurCorrectionExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ schurCorrectionExtension z :=
  (analyticAt_directQuadratic z).sub
    ((((analyticAt_const (v := (backgroundAmplitude : ℂ)⁻¹)).smul (analyticAt_leftCouplingExtension z)).mul
      (analyticAt_complementInverseExtension z hz)).mul
        ((analyticAt_const (v := (backgroundAmplitude : ℂ)⁻¹)).smul (analyticAt_rightCouplingExtension z)))

theorem analyticAt_effectiveSchurExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ effectiveSchurExtension z :=
  (analyticAt_leadingCluster z).add
    ((analyticAt_const (v := (backgroundAmplitude : ℂ))).smul (analyticAt_schurCorrectionExtension z hz))

/-- Fixed compression, defined even for maps that do not preserve the cluster. -/
def compress (A : FiberMap) : ClusterMap :=
  ((clusterProjection.comp A).codRestrict clusterSpace (fun u =>
    (mem_clusterSpace_iff _).mpr (clusterProjection_idempotent (A u)))).comp
      clusterSpace.subtypeL

theorem compress_apply (A : FiberMap) (u : clusterSpace) :
    (compress A u).val = clusterProjection (A u.val) := rfl

def compressionLinear : FiberMap →ₗ[ℂ] ClusterMap where
  toFun := compress
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change clusterProjection (A u.val + B u.val) = _
    rw [map_add]
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change clusterProjection (c • A u.val) = _
    rw [map_smul]
    rfl

theorem compress_norm_le (A : FiberMap) : ‖compress A‖ ≤ ‖A‖ := by
  apply (compress A).opNorm_le_bound (norm_nonneg A)
  intro u
  change ‖clusterProjection (A u.val)‖ ≤ ‖A‖ * ‖u.val‖
  exact (clusterProjection.le_opNorm (A u.val)).trans
    ((mul_le_mul_of_nonneg_right clusterProjection_norm_le (norm_nonneg _)).trans
      (by simpa only [one_mul] using A.le_opNorm u.val))

def compressionCLM : FiberMap →L[ℂ] ClusterMap :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := FiberMap) (F := ClusterMap)
    (σ := RingHom.id ℂ) compressionLinear 1 (fun A => by
    change ‖compress A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using compress_norm_le A)

theorem compressionCLM_eq_restrict (A : FiberMap)
    (hA : ∀ u, clusterProjection (A u) = A u) :
    compressionCLM A = restrictToCluster A hA := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  exact hA u.val

/-- Total finite-dimensional correction, suitable for Cauchy estimates. -/
def finiteCorrectionExtension (z : Parameter) : ClusterMap :=
  compressionCLM (schurCorrectionExtension z)

def finiteSchurExtension (z : Parameter) : ClusterMap :=
  compressionCLM (effectiveSchurExtension z)

theorem finiteCorrectionExtension_eq (z : Parameter) (hz : InBox z) :
    finiteCorrectionExtension z = finiteCorrection z.1 z.2 hz.1 hz.2 := by
  rw [finiteCorrectionExtension, schurCorrectionExtension_eq z hz,
    compressionCLM_eq_restrict _ (clusterProjection_schurCorrection z.1 z.2 hz.1 hz.2)]
  rfl

theorem finiteSchurExtension_eq (z : Parameter) (hz : InBox z) :
    finiteSchurExtension z = finiteSchur z.1 z.2 hz.1 hz.2 := by
  rw [finiteSchurExtension, effectiveSchurExtension_eq z hz,
    compressionCLM_eq_restrict _ (clusterProjection_effectiveSchur z.1 z.2 hz.1 hz.2)]
  rfl

theorem analyticAt_finiteCorrectionExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ finiteCorrectionExtension z :=
  AnalyticAt.comp (f := schurCorrectionExtension) (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := FiberMap) (F := ClusterMap)
    compressionCLM (schurCorrectionExtension z))
    (analyticAt_schurCorrectionExtension z hz)

theorem analyticAt_finiteSchurExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ finiteSchurExtension z :=
  AnalyticAt.comp (f := effectiveSchurExtension) (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := FiberMap) (F := ClusterMap)
    compressionCLM (effectiveSchurExtension z))
    (analyticAt_effectiveSchurExtension z hz)

theorem finiteCorrectionExtension_norm_le_256 (z : Parameter) (hz : InBox z) :
    ‖finiteCorrectionExtension z‖ ≤ 256 := by
  rw [finiteCorrectionExtension_eq z hz]
  exact finiteCorrection_norm_le_256 z.1 z.2 hz.1 hz.2

theorem finiteCorrectionExtension_norm_lt_129 (z : Parameter) (hz : InBox z) :
    ‖finiteCorrectionExtension z‖ < 129 := by
  rw [finiteCorrectionExtension_eq z hz]
  exact finiteCorrection_norm_lt_129 z.1 z.2 hz.1 hz.2

theorem analyticOnNhd_finiteCorrectionExtension :
    AnalyticOnNhd ℂ finiteCorrectionExtension OpenBox :=
  fun z hz => analyticAt_finiteCorrectionExtension z (openBox_inBox hz)

theorem analyticOnNhd_finiteSchurExtension :
    AnalyticOnNhd ℂ finiteSchurExtension OpenBox :=
  fun z hz => analyticAt_finiteSchurExtension z (openBox_inBox hz)

end Maxwell.Continuum.FiberAnalytic
