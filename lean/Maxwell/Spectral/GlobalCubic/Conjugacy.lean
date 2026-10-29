import Maxwell.Spectral.GlobalCubic.Unitary
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (Electric)
open Maxwell.Certificate.FourierBinding (boundaryMomentum)
open scoped Matrix
set_option maxHeartbeats 1200000
noncomputable section

theorem edgeAction_sub (g : Generator) (a : ℤ) (v w : RawField) :
    edgeAction g a (v-w) = edgeAction g a v-edgeAction g a w := by
  funext j r
  cases g <;> fin_cases j <;> simp [edgeAction, sub_eq_add_neg, add_comm]

theorem edgeAction_smul (g : Generator) (a : ℤ) (z : ℂ) (v : RawField) :
    edgeAction g a (z • v) = z • edgeAction g a v := by
  funext j r
  cases g <;> fin_cases j <;> simp [edgeAction, smul_eq_mul]

theorem electric_action (material : Cell20 → ℝ) (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (v : RawField) :
    rawElectric material (edgeAction g a v) = edgeAction g a (rawElectric material v) := by
  change rawCurlAdjoint (rawCurl (edgeAction g a v)) - (1/64:ℂ) • rawMass material (edgeAction g a v) =
    edgeAction g a (rawCurlAdjoint (rawCurl v) - (1/64:ℂ) • rawMass material v)
  rw [gram_edgeAction, hmass, edgeAction_sub, edgeAction_smul]

theorem extendField_injective (k : Momentum) : Function.Injective (extendField k) := by
  intro v w h
  have hh := congrArg restrict h
  simpa only [restrict_extend] using hh

theorem fiber_transform (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (c : Momentum) (v : Electric → ℂ) :
    PrimitiveYee.fiber material (boundaryMomentum (momentum g c)) *ᵥ transform g a c v =
      transform g a c (PrimitiveYee.fiber material (boundaryMomentum c) *ᵥ v) := by
  apply extendField_injective (boundaryMomentum (momentum g c))
  rw [extend_electric material hmat, extend_transform, electric_action material g a hmass,
    extend_transform, extend_electric material hmat]

theorem fiber_intertwining (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (c : Momentum) :
    PrimitiveYee.fiber material (boundaryMomentum (momentum g c)) * matrix g a c =
      matrix g a c * PrimitiveYee.fiber material (boundaryMomentum c) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simpa only [← Matrix.mulVec_mulVec, matrix_mulVec] using fiber_transform material hmat g a hmass c v

theorem fiber_conjugacy (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (c : Momentum) :
    (matrix g a c).conjTranspose * PrimitiveYee.fiber material (boundaryMomentum (momentum g c)) *
      matrix g a c = PrimitiveYee.fiber material (boundaryMomentum c) := by
  rw [Matrix.mul_assoc, fiber_intertwining material hmat g a hmass c,
    ← Matrix.mul_assoc, matrix_adjoint_mul, Matrix.one_mul]

theorem fiber_linear_conjugacy (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (c : Momentum) :
    (unitaryEquiv g a c).toLinearEquiv.conj
      (PrimitiveYee.fiber material (boundaryMomentum c)).toEuclideanLin =
      (PrimitiveYee.fiber material (boundaryMomentum (momentum g c))).toEuclideanLin := by
  have h := congrArg (fun M => M * (matrix g a c).conjTranspose)
    (fiber_intertwining material hmat g a hmass c)
  have hnew : matrix g a c * PrimitiveYee.fiber material (boundaryMomentum c) *
      (matrix g a c).conjTranspose = PrimitiveYee.fiber material (boundaryMomentum (momentum g c)) := by
    simpa only [Matrix.mul_assoc, matrix_mul_adjoint, Matrix.mul_one] using h.symm
  apply LinearMap.ext
  intro x
  change (matrix g a c).toEuclideanLin
    ((PrimitiveYee.fiber material (boundaryMomentum c)).toEuclideanLin
      ((matrix g a c).conjTranspose.toEuclideanLin x)) = _
  have hh := congrArg (fun M : Matrix Electric Electric ℂ => M.toEuclideanLin x) hnew
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hh

theorem fiber_eigenvalues (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (g : Generator) (a : ℤ)
    (hmass : ∀ v, rawMass material (edgeAction g a v) = edgeAction g a (rawMass material v))
    (c : Momentum)
    (hA : (PrimitiveYee.fiber material (boundaryMomentum c)).toEuclideanLin.IsSymmetric)
    (hB : (PrimitiveYee.fiber material (boundaryMomentum (momentum g c))).toEuclideanLin.IsSymmetric) :
    hA.eigenvalues rfl = hB.eigenvalues rfl := by
  apply (hA.eigenvalues_eq_eigenvalues_iff rfl hB rfl).mpr
  rw [← fiber_linear_conjugacy material hmat g a hmass c]
  exact ((unitaryEquiv g a c).toLinearEquiv.charpoly_conj _).symm

end
end Maxwell.Spectral.GlobalCubic
