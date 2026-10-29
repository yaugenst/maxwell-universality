import Maxwell.Green.PhysicalUpper
import Maxwell.Green.RateGeometry
import Maxwell.Realization.Spacing

/-! Rational spacing data for the same physical weighted resolvent block.
The integer placement, full-block bound, and axial scalar asymptotics are
kept tied to one operator and one finite source. -/
namespace Maxwell.Realization

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.PhysicalCompression Maxwell.Green.PhysicalAnalytic
open Filter Matrix
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000

def latticeLength (n : Site) : ℕ := ∑ j, (n j).natAbs

theorem latticeLength_cast (n : Site) :
    (latticeLength n : ℝ) = ∑ j, |(n j : ℝ)| := by
  simp [latticeLength, Nat.cast_natAbs, Int.cast_abs]

def integerPlacementReal (B : Matrix (Fin 3) (Fin 3) ℤ) : Mat3 :=
  fun i j => (B i j : ℝ)

/-- The integer placement does not identify different logical vertices. -/
theorem integerPlacement_injective (B : Matrix (Fin 3) (Fin 3) ℤ)
    (hB : IsUnit (integerPlacementReal B)) :
    Function.Injective (Matrix.mulVec B) := by
  intro x y hxy
  have hc : integerPlacementReal B *ᵥ (fun j => (x j : ℝ)) =
      integerPlacementReal B *ᵥ (fun j => (y j : ℝ)) := by
    funext i
    have h := congrArg (fun z : Site => (z i : ℝ)) hxy
    simpa only [integerPlacementReal, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul] using h
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hB
  have hh := hinj hc
  funext j
  exact_mod_cast congrFun hh j

/-- An ellipsoid bound on the actual inverse yields exponential decay on
the actual integer sublattice, measured in the logical taxicab distance. -/
theorem weightedBlock_lattice_upper {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) (E : ℝ)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    (P Q : MomentumSpace →L[ℝ] MomentumSpace)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hI : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ → ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates q + Complex.I • complexifyCoordinates β.ofLp)).IsInvertible)
    (B : Matrix (Fin 3) (Fin 3) ℤ) (L : ℝ)
    (hmetric : ∀ n : Site, L * (latticeLength n : ℝ) ≤ ‖P (integerMomentum (B *ᵥ n))‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Site,
      ‖weightedBlock edges W
        (Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material)) K hK hm -
          (E : ℂ) • 1)) (B *ᵥ n)‖ ≤ C * Real.exp (-(ρ * L) * (latticeLength n : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := physical_block_ellipsoid_upper edges W material K hK hm E hE
    P Q hPQ hQP hsym ρ hρ hI
  refine ⟨C, hC, fun n => (hb (B *ᵥ n)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (hmetric n) hρ
  nlinarith

/-- Rational bounds and the finite common threshold are selected from the
actual full-torus asymptotics. No lower-rate or successful spacing witness
is assumed. The lower prefactor is exactly one after exponential absorption. -/
theorem exists_physical_spacingPlatform {N : ℕ}
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (T : Field →L[ℂ] Field)
    (u : EuclideanSpace ℂ (Fin N)) (B : Matrix (Fin 3) (Fin 3) ℤ)
    (C U V : ℝ) (hC : 0 < C) (hV : 0 < V) (hVU : V < 2 * U)
    (hupper : ∀ n : Site, ‖weightedBlock edges W T (B *ᵥ n)‖ ≤
      C * Real.exp (-U * (latticeLength n : ℝ)))
    (D : (j : Fin 3) → TorusLocalAssemblyData (fun i => B i j))
    (θ σ : Fin 3 → ℝ) (hσ : ∀ j, σ j ≤ V)
    (hamp : ∀ j, (D j).saddle.amplitude0 ≠ 0)
    (hscalar : ∀ j (d : ℕ), inner ℂ u
      (weightedBlock edges W T ((d : ℤ) • (fun i => B i j)) u) =
        (D j).fullScalarGreen (θ j) (σ j) d)
    (minimum : ℕ) :
    ∃ (P : SpacingPlatform) (C₀ : ℚ),
      P.c = 1 ∧ 1 ≤ C₀ ∧ 256 * C₀ ≤ P.errorConstant ∧ minimum ≤ P.minimumDistance ∧
      (∀ n : Site, ‖weightedBlock edges W T (B *ᵥ n)‖ ≤
        (C₀ : ℝ) * (P.r : ℝ) ^ latticeLength n) ∧
      ∀ d ≥ P.minimumDistance, ∀ j : Fin 3,
        (P.a : ℝ)^d ≤ ‖inner ℂ u
          (weightedBlock edges W T ((d : ℤ) • (fun i => B i j)) u)‖ := by
  obtain ⟨r, a, hr, hr1, ha, ha1, hrU, hra, haV⟩ := exists_rational_rates U V hV hVU
  have hlower : ∀ᶠ d : ℕ in atTop, ∀ j : Fin 3,
      (a : ℝ)^d ≤ ‖inner ℂ u
        (weightedBlock edges W T ((d : ℤ) • (fun i => B i j)) u)‖ := by
    apply Filter.eventually_all.mpr
    intro j
    simpa only [hscalar] using (D j).fullScalarGreen_geometric_lower (hamp j)
      (θ j) (σ j) a ha (lower_rate_of_exponent_le a (σ j) V haV (hσ j))
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.mp hlower
  obtain ⟨C₀, hC₀⟩ := exists_rat_gt (max 1 C)
  have hC₀1 : (1 : ℚ) ≤ C₀ := by
    exact_mod_cast (le_max_left (1 : ℝ) C).trans hC₀.le
  have hCC₀ : C ≤ (C₀ : ℝ) := (le_max_right (1 : ℝ) C).trans hC₀.le
  let P : SpacingPlatform := {
    r := r, a := a, c := 1, errorConstant := 256 * C₀,
    minimumDistance := max minimum d₀,
    r_pos := by exact_mod_cast hr,
    r_lt_one := by exact_mod_cast hr1,
    a_pos := by exact_mod_cast ha,
    a_lt_one := by exact_mod_cast ha1,
    rates_separated := by exact_mod_cast hra,
    c_pos := by norm_num,
    errorConstant_ge_one := by linarith }
  refine ⟨P, C₀, rfl, hC₀1, le_rfl, le_max_left _ _, ?_, ?_⟩
  · intro n
    calc
      _ ≤ C * Real.exp (-U * (latticeLength n : ℝ)) := hupper n
      _ ≤ C * (r : ℝ)^latticeLength n :=
        mul_le_mul_of_nonneg_left (exp_decay_le_geometric U r hrU.le _) hC.le
      _ ≤ (C₀ : ℝ) * (P.r : ℝ)^latticeLength n :=
        mul_le_mul_of_nonneg_right hCC₀ (pow_nonneg hr.le _)
  · intro d hd j
    exact hd₀ d ((le_max_right minimum d₀).trans hd) j

end
end Maxwell.Realization
