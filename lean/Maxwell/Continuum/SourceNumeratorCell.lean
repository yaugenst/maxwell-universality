import Maxwell.Continuum.SourceNumeratorSupport
import Maxwell.Continuum.PhysicalFiberL1Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Uniform analytic physical cell waves on the actual compact source ball.
The exponential is constructed in the Banach algebra of continuous functions,
so analyticity holds in the supremum norm before integration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber CellBandFourier PeriodicBand Set Metric

abbrev SourceBall (h : ℝ) := closedBall (0 : Space) h⁻¹

instance sourceBall_compactSpace (h : ℝ) : CompactSpace (SourceBall h) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space) h⁻¹)

def sourceCellLinear (h : ℝ) : FiberL1.Space →ₗ[ℂ] C(SourceBall h, Polarization) where
  toFun u := ⟨fun x => cellEvaluationL1 x.val u, by
    simp only [cellEvaluationL1_eq]
    exact (continuous_const : Continuous (fun _ : SourceBall h => Complex.I)).smul
      ((antiperiodicField_continuous (FiberL1.inclusion u)).comp continuous_subtype_val)⟩
  map_add' u v := by
    apply ContinuousMap.ext
    intro x
    exact map_add (cellEvaluationL1 x.val) u v
  map_smul' c u := by
    apply ContinuousMap.ext
    intro x
    exact map_smul (cellEvaluationL1 x.val) c u

def sourceCell (h : ℝ) : FiberL1.Space →L[ℂ] C(SourceBall h, Polarization) :=
  (sourceCellLinear h).mkContinuous 1 (fun u => by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    exact (cellEvaluationL1 x.val).le_of_opNorm_le (cellEvaluationL1_norm x.val) u)

theorem sourceCell_apply (h : ℝ) (u : FiberL1.Space) (x : SourceBall h) :
    sourceCell h u x = cellEvaluationL1 x.val u := rfl

theorem sourceCell_physical (h : ℝ) {q : Momentum} (hq : q ∈ physicalChart)
    (x : SourceBall h) :
    sourceCell h (physicalFiberL1 q) x = cellEigenfunction (unscale q) x.val := by
  rw [sourceCell_apply, cellEvaluationL1_eq, inclusion_physicalFiberL1 hq]
  rfl

def sourceExponentLinear (h : ℝ) : Momentum →ₗ[ℂ] C(SourceBall h, ℂ) where
  toFun q := ⟨fun x => Complex.I * ∑ j : Fin 3, q j * (x.val j : ℂ), by fun_prop⟩
  map_add' q p := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk, Pi.add_apply,
      add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c q := by
    ext x
    change Complex.I * (∑ j : Fin 3, (c * q j) * (x.val j : ℂ)) =
      c * (Complex.I * ∑ j : Fin 3, q j * (x.val j : ℂ))
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

def sourceExponent (h : ℝ) : Momentum →L[ℂ] C(SourceBall h, ℂ) :=
  (sourceExponentLinear h).toContinuousLinearMap

def sourcePhase (h : ℝ) (q : Momentum) : C(SourceBall h, ℂ) :=
  NormedSpace.exp (sourceExponent h q)

theorem sourcePhase_apply (h : ℝ) (q : Momentum) (x : SourceBall h) :
    sourcePhase h q x = spatialPhase q x.val := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
    (ContinuousMap.evalCLM ℂ x).continuous (sourceExponent h q)
  rw [← Complex.exp_eq_exp_ℂ] at he
  exact he

theorem sourcePhase_analytic (h : ℝ) (q : Momentum) : AnalyticAt ℂ (sourcePhase h) q :=
  (NormedSpace.exp_analytic (𝕂 := ℂ) (sourceExponent h q)).comp
    (f := sourceExponent h) ((sourceExponent h).analyticAt q)

def sourceCellWave (h : ℝ) (q : Momentum) : C(SourceBall h, Polarization) :=
  sourcePhase h q • sourceCell h (physicalFiberL1 q)

instance sourceCell_isBoundedSMul (h : ℝ) :
    IsBoundedSMul C(SourceBall h, ℂ) C(SourceBall h, Polarization) :=
  IsBoundedSMul.of_norm_smul_le (fun f g => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg f) (norm_nonneg g))).mpr
    intro x
    rw [ContinuousMap.smul_apply', norm_smul]
    exact mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x)
      (norm_nonneg _) (norm_nonneg _))

instance sourceCell_scalarTower (h : ℝ) :
    IsScalarTower ℂ C(SourceBall h, ℂ) C(SourceBall h, Polarization) where
  smul_assoc c f g := by
    apply ContinuousMap.ext
    intro x
    exact smul_assoc c (f x) (g x)

instance sourceCell_smulCommClass (h : ℝ) :
    SMulCommClass ℂ C(SourceBall h, ℂ) C(SourceBall h, Polarization) where
  smul_comm c f g := by
    apply ContinuousMap.ext
    intro x
    exact smul_comm c (f x) (g x)

theorem sourceCellWave_apply (h : ℝ) {q : Momentum} (hq : q ∈ physicalChart)
    (x : SourceBall h) :
    sourceCellWave h q x = spatialPhase q x.val • cellEigenfunction (unscale q) x.val := by
  rw [sourceCellWave, ContinuousMap.smul_apply', sourcePhase_apply, sourceCell_physical h hq]

theorem sourceCellWave_curve_analytic (h : ℝ) {g : ℂ → Momentum} {U : Set ℂ}
    (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U physicalChart) :
    AnalyticOnNhd ℂ (fun z => sourceCellWave h (g z)) U := by
  intro z hz
  exact ((sourcePhase_analytic h (g z)).comp (f := g) (hg z hz)).smul
    (((sourceCell h).analyticAt _).comp (f := fun z => physicalFiberL1 (g z))
      (physicalFiberL1_curve_analytic hU hg hmap z hz))

#print axioms sourcePhase_apply
#print axioms sourceCellWave_curve_analytic

end Maxwell.Continuum.EffectiveMass
