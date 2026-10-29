import Maxwell.Continuum.InvariantRestrictionTransport
import Maxwell.Continuum.HighSchurCrossing

/-! Finite spectral counting derived from an actual unbounded family. The
input inequalities are on D(A) in the original Hilbert space. Orthogonal
unitary transport proves the block energy inequalities used in elimination. -/

noncomputable section

namespace Maxwell.Continuum

open FormPerturbation SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable [FiniteDimensional ℂ K]

namespace InvariantRestriction.Data

variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)

/-- The actual domain vector with prescribed low and high components. -/
def joinedDomain (x : K) (y : highDomain A K) : A.domain :=
  (F.domainEquiv hA).symm (HighSchur.pairDomain (A := F.highOperator hA) x y)

omit [FiniteDimensional ℂ K] in
theorem joinedDomain_norm_sq (x : K) (y : highDomain A K) :
    ‖(F.joinedDomain hA x y : H)‖ ^ 2 = ‖x‖ ^ 2 + ‖(y : Kᗮ)‖ ^ 2 := by
  change ‖K.orthogonalDecomposition.symm
    (WithLp.toLp 2 (x, (y : Kᗮ)))‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- The Schur block energy equals the original unbounded quadratic form. -/
theorem energy_eq_ambient (B : H →L[ℂ] H) (hB : B.IsSymmetric)
    (x : K) (y : highDomain A K) :
    HighSchur.energy (A := F.highBlock hA B) (F.lowBlock B) (coupling (K := K) B) x y =
      (inner ℂ (F.joinedDomain hA x y : H)
        (addBounded A B (F.joinedDomain hA x y))).re := by
  rw [HighSchur.energy_eq_block]
  rw [joinedDomain, F.block_intertwine_symm hA B hB, F.domainEquiv_symm_coe]
  rw [LinearIsometryEquiv.inner_map_map]
  rfl

omit [CompleteSpace K] [FiniteDimensional ℂ K] in
theorem highBlock_energy_eq (B : H →L[ℂ] H) (y : highDomain A K) :
    (inner ℂ (y : Kᗮ) (F.highBlock hA B y)).re =
      (inner ℂ (highInclusion A K y : H)
        (addBounded A B (highInclusion A K y))).re := by
  change (inner ℂ (y : Kᗮ)
    (F.highOperator hA y + Compression.compress Kᗮ B y)).re =
      (inner ℂ ((y : Kᗮ) : H) (A (highInclusion A K y) + B ((y : Kᗮ) : H))).re
  rw [inner_add_right, inner_add_right, Compression.inner_compress]
  rfl

end InvariantRestriction.Data

namespace InvariantRestrictionCrossing

open InvariantRestriction.Data

/-- Physical hypotheses on the full unbounded family and its high directions.
No finite Schur inequality, inverse, or spectral counting conclusion is assumed. -/
structure Family (W : Set ℝ) (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) where
  perturbation : W → H →L[ℂ] H
  symmetric : ∀ t, (perturbation t).IsSymmetric
  high_coercive : ∀ t (u : A.domain), (u : H) ∈ Kᗮ →
    (3 / 4 : ℝ) * ‖(u : H)‖ ^ 2 ≤
      (inner ℂ (u : H) (addBounded A (perturbation t) u)).re
  decrease : ∀ a b : W, (a : ℝ) ≤ b → ∀ u : A.domain,
    (inner ℂ (u : H) (addBounded A (perturbation b) u)).re ≤
      (inner ℂ (u : H) (addBounded A (perturbation a) u)).re -
        ((b : ℝ) - a) * ‖(u : H)‖ ^ 2

namespace Family

variable {W : Set ℝ} (G : Family W A K)
variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)

/-- Construct the low/high family by the actual orthogonal decomposition. -/
def blockFamily : HighSchurCrossing.Family W K Kᗮ where
  high t := F.highBlock hA (G.perturbation t)
  low t := F.lowBlock (G.perturbation t)
  coupling t := InvariantRestriction.Data.coupling (K := K) (G.perturbation t)
  high_selfAdjoint t := F.highBlock_selfAdjoint hA _ (G.symmetric t)
  low_symmetric t := F.lowBlock_symmetric hA _ (G.symmetric t)
  common_domain _ _ := rfl
  high_coercive t y := by
    rw [F.highBlock_energy_eq]
    exact G.high_coercive t (highInclusion A K y) y.val.property
  decrease a b hab x y := by
    change HighSchur.energy (A := F.highBlock hA (G.perturbation b))
      (F.lowBlock (G.perturbation b))
      (InvariantRestriction.Data.coupling (K := K) (G.perturbation b)) x y ≤ _
    rw [F.energy_eq_ambient hA _ (G.symmetric b), F.energy_eq_ambient hA _ (G.symmetric a)]
    have h := G.decrease a b hab (F.joinedDomain hA x y)
    rwa [F.joinedDomain_norm_sq] at h

/-- The actual high inverse is constructed from coercivity, with norm ≤4/3. -/
def highInverse (t : W) : BoundedInverse (F.highBlock hA (G.perturbation t)) :=
  (G.blockFamily F hA).highInverse t

theorem highInverse_norm_le (t : W) : ‖(G.highInverse F hA t).map‖ ≤ 4 / 3 :=
  (G.blockFamily F hA).highInverse_norm_le t

def effective (t : W) : K →L[ℂ] K := (G.blockFamily F hA).effective t

/-- A finite cover constructed from the actual family, with its ambient
invertibility and multiplicity characterizations proved below. -/
def singularParameters : Finset ℝ := (G.blockFamily F hA).singularParameters

theorem singularParameters_card_le :
    (G.singularParameters F hA).card ≤ Module.finrank ℂ K :=
  (G.blockFamily F hA).singularParameters_card_le

theorem inverse_iff_not_mem (t : W) :
    Nonempty (BoundedInverse (addBounded A (G.perturbation t))) ↔
      (t : ℝ) ∉ G.singularParameters F hA := by
  rw [F.inverse_iff_block_inverse hA _ (G.symmetric t)]
  exact (G.blockFamily F hA).inverse_iff_not_mem t

def kernelEquiv (t : W) :
    (addBounded A (G.perturbation t)).ker ≃ₗ[ℂ] (G.effective F hA t).ker :=
  F.kernelSchurEquiv hA _ (G.symmetric t) (G.highInverse F hA t)

theorem kernel_finrank_eq (t : W) :
    Module.finrank ℂ (addBounded A (G.perturbation t)).ker =
      Module.finrank ℂ (G.effective F hA t).ker :=
  (G.kernelEquiv F hA t).finrank_eq

end Family
end InvariantRestrictionCrossing

end Maxwell.Continuum
