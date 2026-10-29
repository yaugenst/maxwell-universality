import Maxwell.Continuum.ClusterComplementResolventEquivalence
import Maxwell.Continuum.FiberAnalyticSchur

/-!
# Operator-norm holomorphy of the full continuum resolvent

The total Feshbach formula uses the total finite Schur formula and is
holomorphic wherever that finite operator is invertible. Equality with
an actual maximal-domain two-sided inverse is proved on the full box.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement

theorem analyticAt_operatorComp {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (f : Parameter → Y →L[ℂ] Z) (g : Parameter → X →L[ℂ] Y) (z : Parameter)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (fun w => (f w).comp (g w)) z :=
  AnalyticAt.comp (f := fun w : Parameter => (f w, g w))
    ((ContinuousLinearMap.compL ℂ X Y Z).analyticAt_bilinear (f z,g z)) (hf.prod hg)

def schurLiftExtension (z : Parameter) : FiberMap :=
  clusterProjection - complementInverseExtension z * rightCouplingExtension z

def adjustedSourceExtension (z : Parameter) : FiberSpace →L[ℂ] clusterSpace :=
  clusterProjectionToSpace.comp (1 - leftCouplingExtension z * complementInverseExtension z)

def fullResolventExtension (z : Parameter) : FiberMap :=
  complementInverseExtension z + (backgroundAmplitude : ℂ)⁻¹ •
    ((schurLiftExtension z).comp (clusterSpace.subtypeL.comp
      ((Ring.inverse (finiteSchurExtension z)).comp (adjustedSourceExtension z))))

theorem schurLiftExtension_eq (z : Parameter) (hz : InBox z) :
    schurLiftExtension z = schurLift z.1 z.2 hz.1 hz.2 := by
  rw [schurLiftExtension,complementInverseExtension_eq z hz,rightCouplingExtension_eq z hz.1]
  rfl

theorem adjustedSourceExtension_eq (z : Parameter) (hz : InBox z) :
    adjustedSourceExtension z = adjustedSource z.1 z.2 hz.1 hz.2 := by
  rw [adjustedSourceExtension,leftCouplingExtension_eq z hz.1,complementInverseExtension_eq z hz]
  rfl

theorem fullResolventExtension_eq (z : Parameter) (hz : InBox z) :
    fullResolventExtension z = fullResolvent z.1 z.2 hz.1 hz.2
      (Ring.inverse (finiteSchur z.1 z.2 hz.1 hz.2)) := by
  rw [fullResolventExtension,complementInverseExtension_eq z hz,schurLiftExtension_eq z hz,
    adjustedSourceExtension_eq z hz,finiteSchurExtension_eq z hz]
  rfl

theorem fullResolventExtension_eq_inverse (z : Parameter) (hz : InBox z)
    (hS : IsUnit (finiteSchur z.1 z.2 hz.1 hz.2)) :
    fullResolventExtension z = (inverseFromSchur z.1 z.2 hz.1 hz.2 hS).map :=
  fullResolventExtension_eq z hz

theorem analyticAt_schurLiftExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ schurLiftExtension z :=
  analyticAt_const.sub ((analyticAt_complementInverseExtension z hz).mul
    (analyticAt_rightCouplingExtension z))

theorem analyticAt_adjustedSourceExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ adjustedSourceExtension z :=
  analyticAt_operatorComp (fun _ => clusterProjectionToSpace)
    (fun w => 1 - leftCouplingExtension w * complementInverseExtension w) z
    analyticAt_const (analyticAt_const.sub ((analyticAt_leftCouplingExtension z).mul
      (analyticAt_complementInverseExtension z hz)))

theorem analyticAt_finiteSchurInverse (z : Parameter) (hz : InBox z)
    (hS : IsUnit (finiteSchurExtension z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (finiteSchurExtension w)) z := by
  have hi : AnalyticAt ℂ (fun A : ClusterMap => Ring.inverse A) (finiteSchurExtension z) := by
    obtain ⟨U,hU⟩ := hS
    rw [← hU]
    exact analyticAt_inverse (𝕜 := ℂ) (A := ClusterMap) U
  exact AnalyticAt.comp (f := finiteSchurExtension) hi (analyticAt_finiteSchurExtension z hz)

/-- The actual complete resolvent is holomorphic in ambient ℓ² operator norm. -/
theorem analyticAt_fullResolventExtension (z : Parameter) (hz : InBox z)
    (hS : IsUnit (finiteSchurExtension z)) : AnalyticAt ℂ fullResolventExtension z := by
  have hi := analyticAt_operatorComp (fun w => Ring.inverse (finiteSchurExtension w))
    adjustedSourceExtension z (analyticAt_finiteSchurInverse z hz hS)
      (analyticAt_adjustedSourceExtension z hz)
  have hm := analyticAt_operatorComp (fun _ => clusterSpace.subtypeL)
    (fun w => (Ring.inverse (finiteSchurExtension w)).comp (adjustedSourceExtension w)) z
      analyticAt_const hi
  exact (analyticAt_complementInverseExtension z hz).add
    ((analyticAt_const (v := (backgroundAmplitude : ℂ)⁻¹)).smul
      (analyticAt_operatorComp schurLiftExtension _ z (analyticAt_schurLiftExtension z hz) hm))

theorem fullResolventExtension_norm_le (z : Parameter) (hz : InBox z) :
    ‖fullResolventExtension z‖ ≤ 2 + 4 * backgroundAmplitude⁻¹ *
      ‖Ring.inverse (finiteSchurExtension z)‖ := by
  rw [fullResolventExtension_eq z hz,finiteSchurExtension_eq z hz]
  exact fullResolvent_norm_le z.1 z.2 hz.1 hz.2 _

theorem analyticOnNhd_fullResolventExtension :
    AnalyticOnNhd ℂ fullResolventExtension
      {z | z ∈ OpenBox ∧ IsUnit (finiteSchurExtension z)} :=
  fun z hz => analyticAt_fullResolventExtension z (openBox_inBox hz.1) hz.2

end Maxwell.Continuum.FiberAnalytic
