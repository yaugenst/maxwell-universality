import Maxwell.Continuum.PECSchurInverse
import Maxwell.Continuum.PECSchurKernel
import Maxwell.Continuum.PECSchurCoercivity
import Maxwell.Continuum.HilbertCoefficientEnergy
import Maxwell.Continuum.WindowCrossing
import Maxwell.Continuum.HighSchurKernel
import Maxwell.Continuum.HighSchurVariational
import Maxwell.Continuum.HighSchurCrossing
import Maxwell.Continuum.InvariantRestrictionTransport
import Maxwell.Continuum.SelfAdjointResolventDetuning
import Maxwell.Continuum.PECDistribution
import Maxwell.Continuum.FourierCurl
import Maxwell.Continuum.CornerHessian
import Maxwell.Continuum.CornerVelocity
import Maxwell.Continuum.FreeFiberNoncentral
import Maxwell.Continuum.FreeFiberPotential
import Maxwell.Continuum.BoxModesGraph
import Maxwell.Continuum.BoxModesPEC
import Maxwell.Continuum.BoxModesBasis
import Maxwell.Continuum.BoxPolarizationComplex
import Maxwell.Continuum.ModeCount
import Maxwell.Continuum.PECBoxIsolation
import Maxwell.Continuum.PECBoxDetuning
import Maxwell.Continuum.PeriodicMaterial
import Maxwell.Continuum.ClusterComplementKernel
import Maxwell.Continuum.ClusterComplementFinite
import Maxwell.Continuum.FiberL1Eigenvector
import Maxwell.Continuum.BlochQuasimomentum
import Maxwell.Continuum.BlochPeriodicGraph
import Maxwell.Continuum.PeriodicBandHessian
import Maxwell.Continuum.PeriodicPhysicalTaylor
import Maxwell.Continuum.PeriodicPhysicalHessian
import Maxwell.Continuum.PeriodicBandProjection
import Maxwell.Continuum.PeriodicBandResolventBounds
import Maxwell.Continuum.PeriodicBandProjectionAnalytic
import Maxwell.Continuum.PeriodicBandSeparatedBounds
import Maxwell.Continuum.PeriodicBandRealResolvent
import Maxwell.Continuum.FiberNormalizationNormalized
import Maxwell.Continuum.WellFourierTail
import Maxwell.Continuum.WellCutoffGevrey
import Maxwell.Continuum.PlacementMetric
import Maxwell.Continuum.PeriodicBandSeparatedJoint
import Maxwell.Continuum.CellBandFourierAudit
import Maxwell.Continuum.EffectiveMassPacketIntegral
import Maxwell.Continuum.EffectiveMassAuxiliaryReality
import Maxwell.Continuum.WellGap
import Maxwell.Continuum.AliasOperatorPairing
import Maxwell.Continuum.EffectiveMassDiagonal
import Maxwell.Continuum.EffectiveMassMaster
import Maxwell.Continuum.MasterConstantLedger
import Maxwell.Continuum.PhysicalFiberL1Analytic
import Maxwell.Continuum.SourceNumeratorLeading
import Maxwell.Continuum.SourceNumerator
import Maxwell.Continuum.SeparatedSymbolDerivatives
import Maxwell.Continuum.CellFourierUnitary
import Maxwell.Continuum.FourierSobolevCharacterization
import Maxwell.Continuum.SourceNumeratorComplete
import Maxwell.Continuum.PeriodicPoleSource
import Maxwell.Continuum.PeriodicTubeCellSymbol
import Maxwell.Continuum.PeriodicTransverseHessian
import Maxwell.Continuum.PeriodicPoleGradient
import Maxwell.Continuum.AnalyticBallTaylor
import Maxwell.Continuum.TransverseGaussianDiagonal
import Maxwell.Continuum.SeparatedCellPolynomial
import Maxwell.Continuum.CellSpatialRestriction
import Maxwell.Continuum.AlmostAnalyticContourBound
import Lean.Util.CollectAxioms

/-! Complete declaration and axiom inventory for the imported continuum
analytic components. This root does not assert the full reduction theorem. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for imported in env.header.modules do
    if (`Maxwell).isPrefixOf imported.module then
      liftIO <| IO.println s!"CONTINUUM_MODULE\t{imported.module}"
  let mut declarations : Array Name := #[]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if let some moduleName := env.header.modules[idx]? then
        if (`Maxwell).isPrefixOf moduleName.module then
          if info.isTheorem then
            declarations := declarations.push name
          if info matches .axiomInfo _ then
            liftIO <| IO.println s!"CONTINUUM_AXIOM\t{name}"
  declarations := declarations.qsort (fun a b => a.toString < b.toString)
  for name in declarations do
    let axioms ← collectAxioms name
    let names := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CONTINUUM_THEOREM\t{name}\t{names}"
