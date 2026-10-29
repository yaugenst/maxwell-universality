import Maxwell.Green.CenteredExclusion
import Maxwell.Green.PhysicalUniformFamily
import Maxwell.Green.SupportedRates
import Maxwell.Realization.PhysicalRates

/-! One physical spectral edge and its actual finite source give a common
integer placement and rational separated rates for the same Green block. -/
noncomputable section
namespace Maxwell.Green
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open PhysicalAnalytic PhysicalLower SourceProfile PhysicalCompression Maxwell.Realization
open Matrix Set Metric
open scoped InnerProductSpace Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000

theorem integerPlacement_column_ne_zero (B : Matrix (Fin 3) (Fin 3) ℤ)
    (hB : IsUnit (integerPlacementReal B)) (j : Fin 3) : (fun i => B i j) ≠ 0 := by
  intro hz
  have hi := integerPlacement_injective B hB
  have he : B *ᵥ Pi.single j 1 = B *ᵥ 0 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_zero]
    exact hz
  have hj := congrFun (hi he) j
  simp only [Pi.single_eq_same, Pi.zero_apply] at hj
  norm_num at hj

namespace PhysicalSimpleEdgeData
variable {material : Cell20 → ℝ} {edge : ℝ} {θ : RealTorusCoordinates}
variable (S : PhysicalSimpleEdgeData material edge θ)

/-- The operating energy and unit mode may be chosen after the common
threshold and overlap budget. All bounds refer to the same actual
weighted inverse block and the same source mode. -/
theorem exists_physical_spacing_family {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) :
    ∃ (B : Matrix (Fin 3) (Fin 3) ℤ) (ξ₀ budget : ℝ),
      IsUnit (integerPlacementReal B) ∧ 0 < ξ₀ ∧ 0 < budget ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < ξ₀ →
      ∀ u : EuclideanSpace ℂ (Fin N), ‖u‖ = 1 →
      budget * Real.sqrt ξ <
        ‖inner ℂ S.eigenvector (sourceRight edges W (complexifyCoordinates θ) u)‖ ^ 2 →
      (∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t)) ∧
      ∀ minimum : ℕ, ∃ (P : SpacingPlatform) (C₀ : ℚ),
        P.c = 1 ∧ 1 ≤ C₀ ∧ 256 * C₀ ≤ P.errorConstant ∧ minimum ≤ P.minimumDistance ∧
        (∀ n : Site,
          ‖weightedBlock edges W
            (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
              K hK hm - ((edge - ξ : ℝ) : ℂ) • 1)) (B *ᵥ n)‖ ≤
              (C₀ : ℝ) * (P.r : ℝ) ^ latticeLength n) ∧
        ∀ d ≥ P.minimumDistance, ∀ j : Fin 3,
          (P.a : ℝ)^d ≤ ‖inner ℂ u
            (weightedBlock edges W
              (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
                K hK hm - ((edge - ξ : ℝ) : ℂ) • 1))
              ((d : ℤ) • (fun i => B i j)) u)‖ := by
  obtain ⟨D, ξG, budget, hξG, hbudget, hgreen⟩ :=
    S.exists_physical_green_family_uniform edges W K hK hm
  obtain ⟨δ, hδ, hexclude⟩ := S.exists_complex_exclusion
  obtain ⟨Q, P, M, ξR, hM, hξR, hPQ, hQP, hsym, hunit, hdist, hl1, hlevels⟩ :=
    D.exists_whitened_level_geometry hδ
  let B := roundedPlacement M Q
  let ξ₀ := min ξG (min ξR δ)
  have hξ₀ : 0 < ξ₀ := lt_min hξG (lt_min hξR hδ)
  have hB : IsUnit (integerPlacementReal B) := hunit
  refine ⟨B, ξ₀, budget, hB, hξ₀, hbudget, ?_⟩
  intro ξ hξ hξsmall u hu hoverlap
  have hξg : ξ < ξG := hξsmall.trans_le (min_le_left _ _)
  have hξr : ξ < ξR := hξsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hξδ : ξ < δ := hξsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hE, hfamily⟩ := hgreen ξ hξ hξg u hu hoverlap
  obtain ⟨hinner, houter⟩ := hlevels ξ hξ hξr
  let ρ := (1 - (1 : ℝ) / 100) * Real.sqrt (2 * ξ)
  let L := (M : ℝ) * (1 - (1 : ℝ) / 100) / Real.sqrt 3
  let V := (1 + (1 : ℝ) / 100)^2 * ((M : ℝ) * Real.sqrt (2 * ξ))
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hI : ∀ β : MomentumSpace, ‖matrixAction Q β‖ ≤ ρ →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        (shiftedOperator material (edge - ξ)
          (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)).IsInvertible := by
    intro β hβ
    obtain ⟨hn, _, hlevel⟩ := hinner β hβ
    have hn' : ‖β.ofLp‖ < δ := (norm_coordinates_le_euclidean β).trans_lt hn
    have hgap : edge - ξ < (S.value (Complex.I • complexifyCoordinates β.ofLp)).re := by
      change edge - (S.value (Complex.I • complexifyCoordinates β.ofLp)).re < ξ at hlevel
      linarith
    intro q _
    apply CenteredExclusion.centered_invertible_all material (edge - ξ) θ
      (Complex.I • complexifyCoordinates β.ofLp) _ q
    intro p hp
    simpa only [add_assoc] using
      hexclude ξ (by rwa [abs_of_pos hξ]) β.ofLp hn' hgap.le p hp (Or.inr hgap)
  have hPQ' : ∀ x, matrixAction P (matrixAction Q x) = x := by
    intro x
    simp only [matrixAction, ← mul_apply_eq_comp, ← map_mul, hPQ, map_one]
    rfl
  have hQP' : ∀ x, matrixAction Q (matrixAction P x) = x := by
    intro x
    simp only [matrixAction, ← mul_apply_eq_comp, ← map_mul, hQP, map_one]
    rfl
  obtain ⟨C, hC, hupper⟩ := weightedBlock_lattice_upper edges W material K hK hm (edge - ξ) hE
    (matrixAction P) (matrixAction Q) hPQ' hQP' hsym ρ hρ hI B L
    (fun n => by simpa only [latticeLength_cast] using hl1 n)
  have haxes : ∀ j : Fin 3, ∃ (β : MomentumSpace) (A : TorusLocalAssemblyData (fun i => B i j)),
      β ∈ ball (0 : MomentumSpace) D.radius ∧
      imaginaryMomentumLevel S.value edge β = ξ ∧
      IsMaxOn (fun x => inner ℝ (integerMomentum (fun i => B i j)) x) (D.body ξ) β ∧
      0 < inner ℝ (integerMomentum (fun i => B i j)) β ∧ A.saddle.amplitude0 ≠ 0 ∧
      ∀ d : ℕ,
        inner ℂ u (weightedBlock edges W
          (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
            K hK hm - ((edge - ξ : ℝ) : ℂ) • 1)) (fun i => (d : ℤ) * B i j) u) =
          A.fullScalarGreen (integerPairingCLM (fun i => B i j) θ)
            (inner ℝ (integerMomentum (fun i => B i j)) β) d :=
    fun j => hfamily (fun i => B i j) (integerPlacement_column_ne_zero B hB j)
  choose β A hβ hlevel hmax hσpos hamp hscalar using haxes
  have hσ : ∀ j : Fin 3, inner ℝ (integerMomentum (fun i => B i j)) (β j) ≤ V := by
    intro j
    exact roundedPlacement_axial_support_bound M P Q hPQ hsym hdist ξ (β j)
      (houter (β j) ⟨Metric.ball_subset_closedBall (hβ j), (hlevel j).le⟩) j
  obtain ⟨hV, hVU⟩ := roundedPlacement_rate_margin M hM hξ
  refine ⟨hE, ?_⟩
  intro minimum
  exact exists_physical_spacingPlatform edges W _ u B C (ρ * L) V hC hV hVU hupper A
    (fun j => integerPairingCLM (fun i => B i j) θ)
    (fun j => inner ℝ (integerMomentum (fun i => B i j)) (β j)) hσ hamp hscalar minimum

end PhysicalSimpleEdgeData
end Maxwell.Green
