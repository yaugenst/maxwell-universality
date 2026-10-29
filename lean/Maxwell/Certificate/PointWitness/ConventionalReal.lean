import Maxwell.Spectral.RealEigenvector
import Maxwell.Spectral.ConventionalReality
import Maxwell.Spectral.SectorSimplicity
import Maxwell.Certificate.PointWitness.ConventionalCenter

/-!
# A real representative of the actual conventional edge eigenspace

The actual conventional fiber is real at a TRIM. The representative below
keeps the projector of the exact unitary-folded vector, while replacing its
arbitrary complex phase by a real normalized choice.
-/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral
open Maxwell.Spectral.PeriodicYee

noncomputable section

/-- Conventional integer TRIM coordinates corresponding to primitive ones. -/
def conventionalTrimCoordinates (k : PrimitiveYee.Translation) : Direction → ℤ :=
  ![k 0, 2 * k 1 - k 0, 2 * k 2 - k 0]

theorem conventionalMomentum_trim (k : PrimitiveYee.Translation) :
    Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k) =
      ConventionalAnalytic.trim (conventionalTrimCoordinates k) := by
  funext j
  fin_cases j <;>
    simp [Folding.conventionalMomentum, PrimitiveYee.timeReversalMomentum,
      ConventionalAnalytic.trim, conventionalTrimCoordinates] <;> ring

/-- Entrywise reality of the actual frozen conventional matrix in the same
Bloch gauge as the normalized folding vector. -/
theorem conventional_folded_matrix_real (k : PrimitiveYee.Translation)
    (i j : Electric20) :
    (PeriodicYee.fiber Concrete.material
      (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k)) i j).im = 0 := by
  rw [conventionalMomentum_trim]
  have h := congrArg Complex.im
    (ConventionalAnalytic.fiber_trim_real Concrete.material (conventionalTrimCoordinates k) i j)
  change -_ = _ at h
  linarith

/-- Any chosen normalized simple eigenvector of this actual full fiber has
an exactly equal projector with a normalized coordinate-real representative. -/
theorem exists_real_conventional_representative (k : PrimitiveYee.Translation) (E : ℝ)
    (v : EuclideanSpace ℂ Electric20) (hvnorm : ‖v‖ = 1)
    (hv : (PeriodicYee.fiber Concrete.material
      (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin v =
        (E : ℂ) • v)
    (hdim : Module.finrank ℂ (Module.End.eigenspace
      (PeriodicYee.fiber Concrete.material
        (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin
        (E : ℂ)) = 1) :
    ∃ φ : EuclideanSpace ℂ Electric20, ‖φ‖ = 1 ∧
      (PeriodicYee.fiber Concrete.material
        (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin φ =
          (E : ℂ) • φ ∧
      (∀ r, (φ r).im = 0) ∧
      (innerSL ℂ φ).smulRight φ = (innerSL ℂ v).smulRight v :=
  RealEigenvector.exists_real_normalized_representative _ E
    (conventional_folded_matrix_real k) v hvnorm hv hdim

/-- Primitive indexed simplicity and other-sector exclusion construct the
real conventional eigenvector. The projector remains that of the exact
normalized folding lift, rather than a separately chosen spectral line. -/
theorem exists_real_folded_conventional_eigenvector (k : PrimitiveYee.Translation)
    (a : Folding.Coset)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ PrimitiveYee.Electric)))
    (hsimple : ∀ j, j ≠ i →
      (SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) a).eigenvalues rfl j ≠
      (SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) a).eigenvalues rfl i)
    (hexclude : ∀ b : Folding.Coset, b ≠ a → ∀ j,
      (SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) b).eigenvalues rfl j ≠
      (SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) a).eigenvalues rfl i) :
    let E := (SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) a).eigenvalues rfl i
    let v := SectorSimplicity.liftedVector (Folding.foldingMatrix (PrimitiveYee.timeReversalMomentum k)) a
      ((SectorSimplicity.primitive_symmetric (PrimitiveYee.timeReversalMomentum k) a).eigenvectorBasis rfl i)
    ∃ φ : EuclideanSpace ℂ Electric20, ‖φ‖ = 1 ∧
      (PeriodicYee.fiber Concrete.material
        (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin φ =
          (E : ℂ) • φ ∧
      (∀ r, (φ r).im = 0) ∧
      (innerSL ℂ φ).smulRight φ = (innerSL ℂ v).smulRight v := by
  dsimp only
  obtain ⟨hn, he, hd, _⟩ :=
    SectorSimplicity.concrete_folding_simple (PrimitiveYee.timeReversalMomentum k) a i hsimple hexclude
  exact exists_real_conventional_representative k _ _ hn he hd

/-- Replacing the phase of the center vector leaves the already constructed
analytic center projector unchanged. -/
theorem exists_real_conventional_projector_vector (k : PrimitiveYee.Translation) (E : ℝ)
    (v : EuclideanSpace ℂ Electric20) (hvnorm : ‖v‖ = 1)
    (hv : (PeriodicYee.fiber Concrete.material
      (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin v =
        (E : ℂ) • v)
    (hdim : Module.finrank ℂ (Module.End.eigenspace
      (PeriodicYee.fiber Concrete.material
        (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin
        (E : ℂ)) = 1)
    (P0 : EuclideanSpace ℂ Electric20 →L[ℂ] EuclideanSpace ℂ Electric20)
    (hP0 : P0 = (innerSL ℂ v).smulRight v) :
    ∃ φ : EuclideanSpace ℂ Electric20, ‖φ‖ = 1 ∧
      (PeriodicYee.fiber Concrete.material
        (Folding.conventionalMomentum (PrimitiveYee.timeReversalMomentum k))).toEuclideanLin φ =
          (E : ℂ) • φ ∧
      (∀ r, (φ r).im = 0) ∧ P0 = (innerSL ℂ φ).smulRight φ := by
  obtain ⟨φ, hn, he, hr, hp⟩ := exists_real_conventional_representative k E v hvnorm hv hdim
  exact ⟨φ, hn, he, hr, hP0.trans hp.symm⟩

/-- The actual selected conventional center has a real normalized
representative with precisely the center spectral projector used by the
constructed conventional branch. The named finite isolation and
other-sector exclusion remain the only spectral inputs. -/
theorem exists_real_conventional_point_vector (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    ∃ φ : ConventionalPointSpace, ‖φ‖ = 1 ∧
      conventionalPointFiber.toEuclideanLin φ = (pointEnergy : ℂ) • φ ∧
      (∀ r, (φ r).im = 0) ∧
      (innerSL ℂ φ).smulRight φ =
        (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
          (conventionalPointVector hgap hexclude) :=
  exists_real_conventional_representative ![1,1,0] pointEnergy
    (conventionalPointVector hgap hexclude) (conventionalPointVector_norm hgap hexclude)
    (conventionalPointVector_eigen hgap hexclude)
    (conventionalPoint_simple_exists hgap hexclude).1

/-- Any projector produced with the selected conventional spectral basis
has the same real normalized representative. This applies directly to
`P 0` of the conventional analytic-resolvent construction. -/
theorem exists_real_conventional_point_projector_vector (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion)
    (P0 : ConventionalPointSpace →L[ℂ] ConventionalPointSpace)
    (hP0 : P0 = (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
      (conventionalPointVector hgap hexclude)) :
    ∃ φ : ConventionalPointSpace, ‖φ‖ = 1 ∧
      conventionalPointFiber.toEuclideanLin φ = (pointEnergy : ℂ) • φ ∧
      (∀ r, (φ r).im = 0) ∧ P0 = (innerSL ℂ φ).smulRight φ := by
  obtain ⟨φ, hn, he, hr, hp⟩ := exists_real_conventional_point_vector hgap hexclude
  exact ⟨φ, hn, he, hr, hP0.trans hp.symm⟩

/-- One fixed real choice for the coherent-profile construction. -/
def conventionalRealPointVector (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) : ConventionalPointSpace :=
  Classical.choose (exists_real_conventional_point_vector hgap hexclude)

theorem conventionalRealPointVector_norm (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) : ‖conventionalRealPointVector hgap hexclude‖ = 1 :=
  (Classical.choose_spec (exists_real_conventional_point_vector hgap hexclude)).1

theorem conventionalRealPointVector_eigen (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    conventionalPointFiber.toEuclideanLin (conventionalRealPointVector hgap hexclude) =
      (pointEnergy : ℂ) • conventionalRealPointVector hgap hexclude :=
  (Classical.choose_spec (exists_real_conventional_point_vector hgap hexclude)).2.1

theorem conventionalRealPointVector_real (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) (r : Electric20) :
    (conventionalRealPointVector hgap hexclude r).im = 0 :=
  (Classical.choose_spec (exists_real_conventional_point_vector hgap hexclude)).2.2.1 r

theorem conventionalRealPointVector_projector (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    (innerSL ℂ (conventionalRealPointVector hgap hexclude)).smulRight
      (conventionalRealPointVector hgap hexclude) =
    (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
      (conventionalPointVector hgap hexclude) :=
  (Classical.choose_spec (exists_real_conventional_point_vector hgap hexclude)).2.2.2

end
end Maxwell.Certificate.PointWitness
