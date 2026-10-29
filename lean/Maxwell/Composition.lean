import Maxwell.Composition.SourceIdentity
import Maxwell.Composition.Residual
import Maxwell.Composition.Woodbury
import Maxwell.Composition.Complement
import Maxwell.Composition.Mediator
import Maxwell.Composition.BlockModes
import Maxwell.Composition.Calibration
import Maxwell.Composition.Bright
import Maxwell.Composition.Recovery
import Maxwell.Composition.Complex
import Maxwell.Composition.Lattice
import Maxwell.Composition.Interactions
import Maxwell.Composition.FinalReadout
import Maxwell.Composition.TargetRecovery
import Maxwell.Composition.SumCoordinates
import Maxwell.Composition.OrthogonalModes
import Maxwell.Composition.WeightedWoodbury
import Maxwell.Composition.LocalBlocks
import Maxwell.Composition.Conditioning
import Maxwell.Composition.SignedMediator
import Maxwell.Composition.ModeSchur
import Maxwell.Composition.DefectCoordinates
import Maxwell.Composition.Weights
import Maxwell.Composition.PhysicalReadout
import Maxwell.Composition.ModeDecoder
import Maxwell.Composition.SourceRounding
import Maxwell.Composition.PositiveEdges
import Maxwell.Composition.PositiveGraph
import Maxwell.Composition.PositiveInverse
import Maxwell.Composition.PositiveNorm
import Maxwell.Composition.Symmetrization
import Maxwell.Composition.PositiveTransform
import Maxwell.Composition.CircuitColumns
import Maxwell.Composition.SourcePositive
import Maxwell.Composition.SourceResidual
import Maxwell.Composition.PositiveRecovery
import Maxwell.Composition.SourceAmplitude
import Maxwell.Composition.ModePrecision
import Maxwell.Composition.PhysicalSourceNorm
import Maxwell.Composition.ResidualFactor

import Maxwell.Composition.SourceRouting
import Maxwell.Composition.SubdivisionBlocks
import Maxwell.Composition.SubdivisionOperator
import Maxwell.Composition.SubdivisionSchur
import Maxwell.Composition.SourceSubdivision
import Maxwell.Composition.TranslatedStencil
import Maxwell.Composition.FiniteDefectLayout
import Maxwell.Composition.BufferedLayout
import Maxwell.Composition.SourceDefectLayout
import Maxwell.Composition.SourceDefectBounds

/-!
# Finite physical composition

The imported modules prove exact weighted source/Schur identities, construct
full inverse operators, bound their genuine operator norms, control actual
mode calibration and finite stored readout, and reduce arbitrary complex
residual solutions to real ones.  The lattice sums are independent of the
number of occupied sites.

The scalar-cell coordinate factorization, actual orthogonal mode
decomposition, signed mediator block, full inverse, fixed-width mode decoder,
and full-matrix condition-number binding are constructed explicitly. The
actual sparse-source circuit is also symmetrized and converted to a
positive-unit bipartite graph, with its matrix inverse, coordinate selector,
fixed diagonal alphabet, and all-equation residual transfer proved.

The actual routed source graph, its chronological path Schur reduction,
inverse and arbitrary-residual decoder are now constructed. Its vertices
carry the shared scalar-cell defect stencil in an explicit buffered PEC
box, with period-preserving translations, disjoint cells, exact quarter
weights, full scalar-material binding, and whole-box volume bounds.

The complete encoder still has to bind the finite background compression
to the infinite Green blocks and instantiate the local spectral data,
calibrated rational arrays and parameter choices. These remaining
construction obligations are not replaced by a presumed final realization
statement, and this import module does not assert their complete closure.
-/
