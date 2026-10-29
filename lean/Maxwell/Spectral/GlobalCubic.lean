import Maxwell.Spectral.GlobalCubic.Material
import Maxwell.Spectral.GlobalCubic.Mass
import Maxwell.Spectral.GlobalCubic.Conjugacy
import Maxwell.Spectral.ReciprocalCover

/-! Exact cubic covariance of the unperturbed diamond comparator.  The
nonsymmorphic reflection includes its cell translation, edge anchor, component
sign and primitive Bloch phase.  No symmetry of the frozen perturbation is used. -/

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (Electric)
open Maxwell.Certificate.FourierBinding (boundaryMomentum)
open scoped Matrix
noncomputable section

/-- The scalar comparator, including an arbitrary uniform material shift. -/
def comparator (shift : ℝ) : Cell20 → ℝ := fun r => Concrete.baseMaterial r + shift

theorem comparator_mass_action (shift : ℝ) (g : Generator) (v : RawField) :
    rawMass (comparator shift) (edgeAction g 5 v) =
      edgeAction g 5 (rawMass (comparator shift) v) := by
  apply rawMass_action
  intro r
  exact base_shift_scalar_symmetry shift g r

/-- The explicit primitive Bloch matrix is unitarily conjugate under each
of the two coordinate swaps and the affine single-coordinate reflection. -/
theorem comparator_conjugacy (shift : ℝ) (g : Generator) (c : Momentum) :
    (matrix g 5 c).conjTranspose *
        PrimitiveYee.fiber (comparator shift) (boundaryMomentum (momentum g c)) *
      matrix g 5 c = PrimitiveYee.fiber (comparator shift) (boundaryMomentum c) :=
  fiber_conjugacy (comparator shift) (base_shift_fcc shift) g 5
    (comparator_mass_action shift g) c

theorem comparator_linear_conjugacy (shift : ℝ) (g : Generator) (c : Momentum) :
    (unitaryEquiv g 5 c).toLinearEquiv.conj
      (PrimitiveYee.fiber (comparator shift) (boundaryMomentum c)).toEuclideanLin =
      (PrimitiveYee.fiber (comparator shift) (boundaryMomentum (momentum g c))).toEuclideanLin :=
  fiber_linear_conjugacy (comparator shift) (base_shift_fcc shift) g 5
    (comparator_mass_action shift g) c

/-- Sorted eigenvalues are literally equal, including multiplicities. -/
theorem comparator_eigenvalues (shift : ℝ) (g : Generator) (c : Momentum)
    (hA : (PrimitiveYee.fiber (comparator shift) (boundaryMomentum c)).toEuclideanLin.IsSymmetric)
    (hB : (PrimitiveYee.fiber (comparator shift)
      (boundaryMomentum (momentum g c))).toEuclideanLin.IsSymmetric) :
    hA.eigenvalues rfl = hB.eigenvalues rfl :=
  fiber_eigenvalues (comparator shift) (base_shift_fcc shift) g 5
    (comparator_mass_action shift g) c hA hB

@[simp] theorem momentum_swap01 (c : Momentum) : momentum .swap01 c = ReciprocalCover.swap01 c := rfl
@[simp] theorem momentum_swap12 (c : Momentum) : momentum .swap12 c = ReciprocalCover.swap12 c := rfl
@[simp] theorem momentum_reflect0 (c : Momentum) : momentum .reflect0 c = ReciprocalCover.flip 0 c := by
  funext j
  fin_cases j <;> simp [momentum, ReciprocalCover.flip]

end
end Maxwell.Spectral.GlobalCubic
