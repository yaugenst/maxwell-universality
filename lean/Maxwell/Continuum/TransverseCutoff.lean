import Maxwell.Continuum.PECTransverse
import Maxwell.Continuum.InvariantRestriction

/-! The physical finite free-mode cutoff used by the Maxwell spectral count. -/

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

/-- A finite invariant part of the actual transverse curl-curl domain,
leaving free energy at least 26 on its orthogonal complement. -/
structure TransverseCutoff (Ω : Opens Space) where
  space : Submodule ℂ (transverseSpace Ω)
  finite : FiniteDimensional ℂ space
  invariant : InvariantRestriction.Data (transverseCurlCurl Ω) space
  high : ∀ u : (transverseCurlCurl Ω).domain, (u : transverseSpace Ω) ∈ spaceᗮ →
    26 * ‖(u : transverseSpace Ω)‖ ^ 2 ≤
      (inner ℂ (u : transverseSpace Ω) (transverseCurlCurl Ω u)).re

attribute [instance] TransverseCutoff.finite

end Maxwell.Continuum
