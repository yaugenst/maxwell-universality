import Maxwell.Continuum.BoxModesCutoffSpectrum
import Maxwell.Continuum.BoxModesSmooth
import Maxwell.Continuum.BoxModesPolarization
import Maxwell.Continuum.BoxModesTensor
import Maxwell.Continuum.WeakCurl

/-!
# Audit of the explicit continuum PEC mode foundation

These endpoints establish the literal continuum modes, their Euclidean L²
orthogonality and completeness, actual PEC graph membership by smooth cutoff,
and action of the represented curl-curl operator. The resulting complete
Hilbert basis proves the transverse coefficient equation. The physical low
space is finite, lies in the actual operator domain, is invariant, has
dimension at most54 times box volume, and leaves energy at least26 on its
orthogonal complement. Variable-material spectral counting is built on this
cutoff in the separate PEC Schur modules.
-/

namespace Maxwell.Continuum.BoxModesAudit

/-- Both developments use exactly the same physical spatial type. -/
theorem point_type_agrees : BoxModes.Point = Space := rfl

/-- The classical partials and distributional partials use identical vectors. -/
theorem coordinate_directions_agree (j : Fin 3) :
    BoxModes.direction j = coordinateDirection j := rfl

#print axioms BoxModes.contDiff_electric
#print axioms BoxModes.curl_curl_electric
#print axioms BoxModes.gradient_scalarPotential
#print axioms BoxModes.electric_tangential_upper
#print axioms BoxModes.finrank_positive_eigenspace
#print axioms BoxModes.curlCurlSymbol_nonnegative
#print axioms BoxModes.integral_intervalSin_mul
#print axioms BoxModes.integral_intervalCos_mul
#print axioms BoxModes.integral_scalarBoxMode_mul
#print axioms BoxModes.electric_component_eq_scalarBoxMode
#print axioms BoxModes.componentBoxMode_complete
#print axioms BoxModes.componentCurlGraph_mem_pecGraph
#print axioms BoxModes.componentMode_operator_graph
#print axioms BoxModes.componentHilbertBasis
#print axioms BoxModes.longitudinalMode_mem_kernel
#print axioms BoxModes.transverseCurlCurl_coefficient
#print axioms BoxModes.lowTransverseSpace_invariant
#print axioms BoxModes.boxTransverseCutoff
#print axioms BoxModes.boxTransverseCutoff_finrank_le_volume
#print axioms BoxModes.boxTransverseCutoff_finrank_le_physical_volume
#print axioms ModeCount.index_lt_twice_length
#print axioms ModeCount.lowFrequency_polarized_card_le
#print axioms ModeCount.spectralCountBudget_le_volume

end Maxwell.Continuum.BoxModesAudit
