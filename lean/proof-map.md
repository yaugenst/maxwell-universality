# Manuscript and Lean declarations

The labels below refer to the supplementary information in `paper/si/`.
Each row identifies a particular statement and its formal declarations;
the surrounding manuscript theorem can require additional composition and
computation bounds. Exact hypotheses are in the linked source. The scope
registry and `report_scope.py` describe which source bytes have a matching
verification receipt.

## Shared finite mathematics

| Manuscript statement | Module and declarations | Scope |
| --- | --- | --- |
| Sparse input, `si:sec:input` | [Interfaces](Maxwell/Interfaces.lean): `Maxwell.SparseRationalMatrix.toMatrix_at_stored`, `toMatrix_ne_zero_iff` | Exact finite storage and matrix support |
| Dyadic representation | [Interfaces](Maxwell/Interfaces.lean): `Maxwell.Dyadic.denominator_bitLength`, `value_add` | Denominator bit length and exact addition at common precision |
| Mediator and residual elimination, `d:eq:target-mediator`, `d:eq:exact-residual` | [Algebra](Maxwell/Algebra.lean): `Maxwell.physical_mediator_schur`, `schur_residual_identity`, `full_block_factorization` | Block identities with the stated inverse hypotheses |
| Projection residual, `d:eq:app-saddle-residual-identity` | [Algebra](Maxwell/Algebra.lean): `Maxwell.saddle_projected_error` | Exact identity retaining both saddle residual blocks |
| Conditional exponent arithmetic, `d:cor:complexity` | [Complexity](Maxwell/Complexity.lean): `Maxwell.composedExponent_lt_iff`, `composedExponent_not_lt_of_le_floor`, `composedExponent_at_boundary` | The exponent comparison; algorithm transfer additionally requires the realization and computational model |

## Continuum construction

Names in this table have prefix `Maxwell.Continuum.` unless given in full.
These modules are imported by `ContinuumAnalysisAudit.lean`, directly or
through dependencies.

| Manuscript statement | Module and declarations | Scope |
| --- | --- | --- |
| Mode count, `c:lem:count`, `c:eq:count` | [ModeCount](Maxwell/Continuum/ModeCount.lean): `ModeCount.spectralCountBudget_le_volume` | The explicit integer-mode bound `2 ∏ (1 + 2 Nⱼ) ≤ 54 ∏ Nⱼ` |
| Detuning and inverse, `c:lem:detuning`, `c:eq:detuning` | [PECBoxDetuning](Maxwell/Continuum/PECBoxDetuning.lean): `ScalarDielectric.box_detuning_probability`, `box_sampled_resolvent`, `box_detuning_dyadic` | Physical PEC spectrum, dyadic shifts, success probability, and L²/graph inverse bounds |
| Periodic dielectric, `c:eq:background` | [PeriodicMaterial](Maxwell/Continuum/PeriodicMaterial.lean): `PeriodicMaterial.coefficient_bounds`, `dielectric_latticeTranslate` | Scalar coefficient in `[6,8]`, with the stated period |
| Corner Hessian, `c:eq:explicitA0` | [CornerHessian](Maxwell/Continuum/CornerHessian.lean): `Corner.normalized_resolvent_rayleigh`, `hessianCoefficient_bounds` | Exact quadratic forms in `ℚ(√19)`; the Bloch-band identification uses the subsequent analytic modules |
| Master constants, `c:eq:masterconstants`, `c:app:ledger` | [MasterConstants](Maxwell/Continuum/MasterConstants.lean): `MasterConstants.Cs`, `Ls`, `Cs_pow64_le_Ls`; [MasterConstantLedger](Maxwell/Continuum/MasterConstantLedger.lean): `MasterConstants.ledger_below_master`, `length_upper_bound` | `C* = 2^(2^40)`, `L* = 8^ceil(64·2^40/3)`, and the arithmetic majorant ledger |
| Well gap, `c:lem:perron` | [WellGap](Maxwell/Continuum/WellGap.lean): `Well.gap_numeric`, `top_eigenvector_simple`, `well_complement_norm` | Positive top mode, simplicity, and the explicit complementary gap |
| Effective mass, `c:lem:effectivemass` | [EffectiveMassMaster](Maxwell/Continuum/EffectiveMassMaster.lean): `EffectiveMass.exists_effectiveMass_length` | Actual continuum eigenmode, eigenvalue and gap bounds, real structure, approximation, overlap, support, and H¹ bound |
| Pole integral and leading coefficient, `c:eq:pole`, `c:eq:leadingcoefficient` | [PeriodicPoleIntegralAudit](Maxwell/Continuum/PeriodicPoleIntegralAudit.lean): audit of `PeriodicBand.selectedLocalIntegral_asymptotic`, `localSelectedSymbol_fourier_placement`, `selectedLeadingCoefficient_paper_lower` | Cutoff, contour, physical-coordinate integral, and positive leading coefficient |
| Interaction upper and lower bounds, `c:lem:interactions` | [UsefulCoupling](Maxwell/Continuum/UsefulCoupling.lean): `EffectiveMass.physicalWellBlock_norm`, `usefulCoupling_real`, `usefulCoupling_lower` | Actual resolvent blocks and positive axial coupling, with length, parity, separation, and tail conditions |
| Parameter choice, `c:lem:parameters` | [ParameterExecutable](Maxwell/Continuum/ParameterExecutable.lean): `Parameters.encode_spec`, `encode_eq_sourceStage` | Explicit source-specialized choice satisfying spacing, buffer, leakage, and tail tests |
| Precision and inverse scales, `c:eq:inverse-scales` | [ParameterSourcePrecision](Maxwell/Continuum/ParameterSourcePrecision.lean): `Parameters.source_inverse_scales`, `source_tau_bits`, `source_exponential_budgets` | Polynomial inverse budgets and explicit source-dependent bit bounds |
| Volume, `c:eq:volume-final` | [ParameterVolume](Maxwell/Continuum/ParameterVolume.lean): `Parameters.source_box_cells_bound`, `source_physical_volume_bound` | Source-specialized box size and physical volume |
| Finite descriptions, `c:sec:representation` | [ContinuumDescription](Maxwell/Continuum/ContinuumDescription.lean): `RealizationParameters.descriptionBits_polynomial` | Encoded physical description length under the input assumptions |
| Random sampling, `c:lem:detuning` | [ContinuumFairDetuning](Maxwell/Continuum/ContinuumFairDetuning.lean): `RealizationParameters.randomDraw_law`, `randomDraw_bad_probability`, `randomBitCount_linear` | Finite random bits, uniform draw law, failure probability, and seed length |
| Recovery and finite decoding, `c:sec:recovery` | [ContinuumDecoder](Maxwell/Continuum/ContinuumDecoder.lean): `RealizationParameters.decoder_recovery`, `decoder_output_words`, `decoder_runs` | Residual recovery from finite reports and execution by a fixed finite decoder |
| Zero source and smallest input | [ContinuumBaseCases](Maxwell/Continuum/ContinuumBaseCases.lean): `VacuumBox.base_instance`, `physical_volume` | Unit-box continuum inverse and exact no-sample recovery for the stated branches |

The later `SourceRouting*`, `Stored*`, `FourierTensor*`, and calibration
execution modules develop the uniform finite encoder. Their presence in the
source collection is distinct from inclusion in the completed continuum
replay. The full machine-realization theorem requires their final
composition and verification.

## Discrete construction

| Manuscript statement | Module and declarations | Scope |
| --- | --- | --- |
| Yee dimension, `d:eq:yee-dimension` | [Interfaces](Maxwell/Interfaces.lean): `Maxwell.retainedEdge_card` | Exact retained-edge count |
| Cell average and scalar detuning, `d:eq:cell-average`, `d:lem:pec` | [Interfaces](Maxwell/Interfaces.lean): `Maxwell.edgeAverage_bounds`, `edgeAverage_uniform_shift`, `mass_diagonal_uniform_shift` | Material bounds and scalar diagonal shift |
| Finite stencil, `d:lem:pec` | [TargetStencil](Maxwell/TargetStencil.lean): `Maxwell.Target.curl_mulVec_stencil`, `curl_transpose_mulVec_stencil`, `operator_mulVec_stencil` | Equality between the finite matrix action and the local stencil |
| Selected physical platform, `d:prop:physical-platform` | [SelectedPlatform](Maxwell/Composition/SelectedPlatform.lean): `Maxwell.Composition.exists_selected_platform` | Platform construction conditional on `PointClusterComplementGap`, `PointOtherSectorExclusion`, and `PointRealEdgeExclusion` |
| Mode refinement | [SelectedPlatform](Maxwell/Composition/SelectedPlatform.lean): `Maxwell.Composition.SelectedPlatform.modeApproximation_spec`, `weightedApproximation_spec` | Rational approximations to the same certified mode and its weighted readout |

`Maxwell/Certificate/` contains exact arithmetic and generated spectral
proof modules used by this route. The selected discrete audits enumerate
their own declaration dependencies. Numerical solver demonstrations and
finite certificate replay are separate artifacts with separate scopes.
