import Maxwell.Composition.LocalComplement
import Maxwell.Composition.PhysicalReality
import Maxwell.Green.PhysicalSpacing
import Maxwell.Defect.EffectiveCompression

/-! Assemble the physical platform from the accepted actual defect mode and
the actual full Green bounds. The complement and all rational safety constants
are derived here from that same operator and mode. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Green.PhysicalCompression Maxwell.Realization
open scoped InnerProduct
set_option maxHeartbeats 800000

theorem physicalGreenBlock_frozen_zero (D : Finset Site) (z : ℚ) :
    physicalGreenBlock D (Ring.inverse (FiniteStencil.frozenOperator z)) 0 =
      FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        FiniteStencil.frozenEdgeCoefficientQ 13 (by norm_num)
        FiniteStencil.frozenEdgeCoefficientQ_abs z (ScalarDefect.coordinateWeight D) := by
  unfold physicalGreenBlock
  rw [FiniteStencil.weightedInverseCompression_realPart]
  have he : translatedEmbedding (ScalarDefect.edgeEmbedding D) 0 = ScalarDefect.edgeEmbedding D := by
    apply Function.Embedding.ext
    intro i
    change ((ScalarDefect.edgeEmbedding D i).1,
      (ScalarDefect.edgeEmbedding D i).2 - 20 • (0 : Site)) = ScalarDefect.edgeEmbedding D i
    simp
  rw [weightedBlock, he]
  rfl

theorem latticeLength_nat_smul (d : ℕ) (n : Site) :
    latticeLength ((d : ℤ) • n) = d * latticeLength n := by
  simp [latticeLength, Pi.smul_apply, Int.natAbs_mul, Finset.mul_sum]

def operatorEquiv (A : Field →L[ℂ] Field) (hA : IsUnit A) : Field ≃L[ℂ] Field :=
  ContinuousLinearEquiv.equivOfInverse' A (Ring.inverse A)
    (Ring.mul_inverse_cancel A hA) (Ring.inverse_mul_cancel A hA)

@[simp] theorem operatorEquiv_coe (A : Field →L[ℂ] Field) (hA : IsUnit A) :
    (operatorEquiv A hA : Field →L[ℂ] Field) = A := rfl

@[simp] theorem operatorEquiv_symm_coe (A : Field →L[ℂ] Field) (hA : IsUnit A) :
    ((operatorEquiv A hA).symm : Field →L[ℂ] Field) = Ring.inverse A := rfl

theorem exists_operating_platform
    (z : ℚ) (hz : 0 ≤ z) (hu : z ≤ 957 / 100000)
    (D : Finset Site) (hD : D.Nonempty)
    (hunit : IsUnit (FiniteStencil.frozenOperator z))
    (gap : ℚ) (hgap : 0 < gap)
    (hinv : ‖Ring.inverse (FiniteStencil.frozenOperator z)‖ ≤ 1 / (gap : ℝ))
    (u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card)) (μ : ℝ)
    (hmode : ‖u‖ = 1)
    (he : physicalGreenBlock D (Ring.inverse (FiniteStencil.frozenOperator z)) 0 u = μ • u)
    (hs : (physicalGreenBlock D (Ring.inverse (FiniteStencil.frozenOperator z)) 0).toLinearMap.IsSymmetric)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace
      (physicalGreenBlock D (Ring.inverse (FiniteStencil.frozenOperator z)) 0).toLinearMap μ) = 1)
    (hμ : 22 < μ)
    (B : Matrix Direction Direction ℤ) (hB : IsUnit (integerPlacementReal B))
    (P : SpacingPlatform) (C₀ : ℚ) (hC₀ : 1 ≤ C₀) (hc : P.c = 1)
    (hfloor : SourceDefectLayout.radius D + 1 ≤ P.minimumDistance)
    (hupper : ∀ n : Site,
      ‖weightedBlock (ScalarDefect.edgeEmbedding D) (ScalarDefect.coordinateWeight D)
        (Ring.inverse (FiniteStencil.frozenOperator z)) (B.mulVec n)‖ ≤
        (C₀ : ℝ) * (P.r : ℝ) ^ latticeLength n)
    (hlower : ∀ d ≥ P.minimumDistance, ∀ j : Direction,
      (P.a : ℝ)^d ≤ ‖inner ℂ (realCoordinateEmbedding u)
        (weightedBlock (ScalarDefect.edgeEmbedding D) (ScalarDefect.coordinateWeight D)
          (Ring.inverse (FiniteStencil.frozenOperator z))
            ((d : ℤ) • (fun i => B i j)) (realCoordinateEmbedding u))‖) :
    ∃ Q : PhysicalPlatform,
      Q.background = operatingBackground z hz hu ∧ Q.defect = D ∧
      Q.basis = B ∧ Q.spacing.r = P.r ∧ Q.spacing.a = P.a ∧
      Q.spacing.minimumDistance = P.minimumDistance ∧
      Q.eigenvalue = μ ∧ HEq Q.mode u ∧ Q.rowBound = 16 ∧ Q.bulkGap = gap := by
  obtain ⟨γ, e, hγ, hop, heinv⟩ := exists_local_complement
    (physicalGreenBlock D (Ring.inverse (FiniteStencil.frozenOperator z)) 0) u μ
    hmode he hs hsimple
  let C : ℚ := 256 * C₀ + 5 + (2 / γ) * (64 * C₀ + 1)^2
  have hC : 1 ≤ C := by
    have ht : 0 ≤ (2 / γ) * (64 * C₀ + 1)^2 := mul_nonneg (by positivity) (sq_nonneg _)
    dsimp [C]
    linarith
  let P' : SpacingPlatform := { P with errorConstant := C, errorConstant_ge_one := hC }
  let background := operatingBackground z hz hu
  have hback : background.operator = FiniteStencil.frozenOperator z := operating_operator z hz hu
  let bulk := operatorEquiv (FiniteStencil.frozenOperator z) hunit
  have hreal : ∀ x, Ring.inverse (FiniteStencil.frozenOperator z) (star x) =
      star (Ring.inverse (FiniteStencil.frozenOperator z) x) := by
    intro x
    apply inverse_star _ hunit
    rw [← hback]
    exact electricOperator_star _ _ _ _
  let Q : PhysicalPlatform := {
    background := background, defect := D, defect_nonempty := hD,
    bulk := bulk, bulk_operator := hback.symm,
    bulkGap := gap, rowBound := 16, bulkGap_pos := hgap, rowBound_pos := by norm_num,
    bulk_inverse_bound := hinv,
    bulk_norm_bound := by simpa only [bulk, operatorEquiv_coe, ← hback, Rat.cast_ofNat] using background_operator_norm background,
    mode := u, eigenvalue := μ, mode_unit := hmode, mode_equation := he,
    local_symmetric := hs,
    incrementBound := 3 / 32, incrementBound_pos := by norm_num,
    increment_reserve := by norm_num [background, operatingBackground],
    eigenvalue_headroom := by norm_num; linarith,
    defectGap := γ, defectGap_pos := hγ, complement := e,
    complement_operator := hop, complement_inverse_bound := heinv,
    basis := B, basis_injective := integerPlacement_injective B hB,
    spacing := P', radius_floor := hfloor,
    greenConstant := C₀, greenConstant_nonneg := by linarith,
    error_constant := by dsimp [P', C]; norm_cast,
    green_upper := by
      intro d _ n _
      have hh := hupper ((d : ℤ) • n)
      rw [Matrix.mulVec_smul, latticeLength_nat_smul, pow_mul] at hh
      exact hh,
    green_axial := by
      intro d hd j
      have hh := hlower d hd j
      rw [weightedBlock_real_inner_norm _ _ _ hreal] at hh
      have hcol : B.mulVec (unitSite j) = fun i => B i j := by
        exact Matrix.mulVec_single_one B j
      simpa only [P', hc, Rat.cast_one, one_mul, hcol, physicalGreenBlock,
        bulk, operatorEquiv_symm_coe] using hh }
  exact ⟨Q, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, rfl, rfl⟩

end Maxwell.Composition
