import Maxwell.Green.PhysicalCompression
import Maxwell.Green.AngularTorus
import Maxwell.Spectral.YeeAnalytic

/-! Entire finite-source Bloch maps. Left and right continuations are
separate analytic maps and become adjoints on the real momentum slice. -/
namespace Maxwell.Green.SourceProfile

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.PhysicalCompression
open scoped Matrix.Norms.Elementwise
noncomputable section

abbrev ComplexMomentum := Fin 3 → ℂ

def phase (n : Site) (z : ComplexMomentum) : ℂ :=
  Complex.exp (Complex.I * ∑ j, (n j : ℂ) * z j)

theorem phase_analyticAt (n : Site) (z : ComplexMomentum) : AnalyticAt ℂ (phase n) z := by
  apply AnalyticAt.cexp'
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj j : ComplexMomentum →L[ℂ] ℂ).analyticAt z)

def realMomentum (q : Fin 3 → ℝ) : ComplexMomentum := fun j => (q j : ℂ)

theorem phase_real (n : Site) (q : Fin 3 → ℝ) :
    phase n (realMomentum q) = UnitAddTorus.mFourier n (angularTorusPoint q) := by
  rw [mFourier_angularTorusPoint]
  simp [phase, realMomentum, integerPairingCLM_apply]

theorem phase_neg_conjugate_real (n : Site) (q : Fin 3 → ℝ) :
    star (phase n (realMomentum q)) = phase (-n) (realMomentum q) := by
  rw [phase_real, phase_real, UnitAddTorus.mFourier_neg]
  rfl

variable {N : ℕ}

def rightMatrix (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (z : ComplexMomentum) :
    Matrix Edge20 (Fin N) ℂ := fun r i =>
  if r = (edgeCellEquiv (edges i)).1 then
    (Real.sqrt (W i : ℝ) : ℂ) * phase (-(edgeCellEquiv (edges i)).2) z else 0

def leftMatrix (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (z : ComplexMomentum) :
    Matrix (Fin N) Edge20 ℂ := fun i r =>
  if r = (edgeCellEquiv (edges i)).1 then
    (Real.sqrt (W i : ℝ) : ℂ) * phase ((edgeCellEquiv (edges i)).2) z else 0

theorem rightMatrix_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (z : ComplexMomentum) : AnalyticAt ℂ (rightMatrix edges W) z := by
  apply AnalyticAt.pi
  intro r
  apply AnalyticAt.pi
  intro i
  unfold rightMatrix
  split_ifs
  · exact analyticAt_const.mul (phase_analyticAt _ _)
  · exact analyticAt_const

theorem leftMatrix_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (z : ComplexMomentum) : AnalyticAt ℂ (leftMatrix edges W) z := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro r
  unfold leftMatrix
  split_ifs
  · exact analyticAt_const.mul (phase_analyticAt _ _)
  · exact analyticAt_const

/-- Rectangular Euclidean matrix conversion as one actual continuous linear map. -/
def rectangularMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Matrix m n ℂ →L[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rectangularMap_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    rectangularMap A x i = A.mulVec x i := rfl

def sourceRight (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (z : ComplexMomentum) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ Edge20 :=
  rectangularMap (rightMatrix edges W z)

def sourceLeft (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (z : ComplexMomentum) :
    EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  rectangularMap (leftMatrix edges W z)

theorem sourceRight_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (z : ComplexMomentum) : AnalyticAt ℂ (sourceRight edges W) z :=
  ((rectangularMap (m := Edge20) (n := Fin N)).analyticAt _).comp (rightMatrix_analyticAt edges W z)

theorem sourceLeft_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (z : ComplexMomentum) : AnalyticAt ℂ (sourceLeft edges W) z :=
  ((rectangularMap (m := Fin N) (n := Edge20)).analyticAt _).comp (leftMatrix_analyticAt edges W z)

theorem leftMatrix_real (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (q : Fin 3 → ℝ) :
    leftMatrix edges W (realMomentum q) = (rightMatrix edges W (realMomentum q)).conjTranspose := by
  ext i r
  simp only [leftMatrix, rightMatrix, Matrix.conjTranspose_apply]
  split_ifs <;> simp [phase_neg_conjugate_real]

theorem rectangularMap_adjoint {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    rectangularMap A.conjTranspose = (rectangularMap A).adjoint := by
  change A.conjTranspose.toEuclideanLin.toContinuousLinearMap =
    A.toEuclideanLin.toContinuousLinearMap.adjoint
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

theorem sourceLeft_real_adjoint (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (q : Fin 3 → ℝ) :
    sourceLeft edges W (realMomentum q) = (sourceRight edges W (realMomentum q)).adjoint := by
  unfold sourceLeft sourceRight
  rw [leftMatrix_real, rectangularMap_adjoint]

theorem sourceRight_real_apply (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (q : Fin 3 → ℝ) (u : EuclideanSpace ℂ (Fin N)) (r : Edge20) :
    sourceRight edges W (realMomentum q) u r =
      profile edges (Maxwell.Defect.complexSqrtWeightOperator W u) (angularTorusPoint q) r := by
  simp only [sourceRight, rectangularMap_apply, Matrix.mulVec, dotProduct, rightMatrix,
    profile, Maxwell.Defect.complexSqrtWeightOperator_apply, phase_real]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

end
end Maxwell.Green.SourceProfile
