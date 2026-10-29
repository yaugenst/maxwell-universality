import Maxwell.Spectral.PeriodicYee
import Maxwell.Spectral.Bloch
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Entire continuation of the actual conventional-cell Yee fiber.
The formal adjoint reverses complex phases without conjugating momentum. -/
namespace Maxwell.Spectral.ConventionalAnalytic

open Maxwell.Spectral.PeriodicYee
open scoped Matrix.Norms.Elementwise
set_option maxRecDepth 4000
noncomputable section
abbrev ComplexMomentum := Direction → ℂ

def realMomentum (q : Momentum) : ComplexMomentum := fun j => (q j : ℂ)

def boundaryPhase (z : ComplexMomentum) (j : Direction) (r : Cell20) : ℂ :=
  if r j = 19 then Complex.exp (Complex.I * z j) else 1

def difference (z : ComplexMomentum) (j : Direction) : Matrix Cell20 Cell20 ℂ :=
  fun r s => (if s = forwardCell j r then boundaryPhase z j r else 0) -
    (if s = r then 1 else 0)

def curl (z : ComplexMomentum) : Matrix Face20 Electric20 ℂ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then difference z 1 i.2 j.2
    else if j.1 = 1 then -difference z 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then difference z 2 i.2 j.2
    else if j.1 = 2 then -difference z 0 i.2 j.2 else 0
  else
    if j.1 = 1 then difference z 0 i.2 j.2
    else if j.1 = 0 then -difference z 1 i.2 j.2 else 0

def formalAdjointCurl (z : ComplexMomentum) : Matrix Electric20 Face20 ℂ :=
  (curl (-z)).transpose

def fiber (material : Cell20 → ℝ) (z : ComplexMomentum) : Matrix Electric20 Electric20 ℂ :=
  formalAdjointCurl z * curl z - (1/64 : ℂ) • mass material

theorem boundaryPhase_analyticAt (j : Direction) (r : Cell20) (z : ComplexMomentum) :
    AnalyticAt ℂ (fun w => boundaryPhase w j r) z := by
  unfold boundaryPhase
  split_ifs
  · exact (analyticAt_const.mul
      ((ContinuousLinearMap.proj j : ComplexMomentum →L[ℂ] ℂ).analyticAt z)).cexp'
  · exact analyticAt_const

theorem difference_entry_analyticAt (j : Direction) (r s : Cell20) (z : ComplexMomentum) :
    AnalyticAt ℂ (fun w => difference w j r s) z := by
  unfold difference
  split_ifs <;> first
    | exact (boundaryPhase_analyticAt j r z).sub analyticAt_const
    | exact analyticAt_const

theorem curl_entry_analyticAt (i : Face20) (j : Electric20) (z : ComplexMomentum) :
    AnalyticAt ℂ (fun w => curl w i j) z := by
  unfold curl
  split_ifs <;> first
    | exact difference_entry_analyticAt _ _ _ z
    | exact (difference_entry_analyticAt _ _ _ z).neg
    | exact analyticAt_const

theorem curl_analyticAt (z : ComplexMomentum) : AnalyticAt ℂ curl z :=
  AnalyticAt.pi fun i => AnalyticAt.pi fun j => curl_entry_analyticAt i j z

theorem formalAdjointCurl_analyticAt (z : ComplexMomentum) :
    AnalyticAt ℂ formalAdjointCurl z := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  exact (curl_entry_analyticAt j i (-z)).comp analyticAt_id.neg

private theorem matrixProduct_analyticAt {α β γ Z : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (A : Z → Matrix α β ℂ) (B : Z → Matrix β γ ℂ) (z : Z)
    (hA : AnalyticAt ℂ A z) (hB : AnalyticAt ℂ B z) :
    AnalyticAt ℂ (fun w => A w * B w) z := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  change AnalyticAt ℂ (fun w => ∑ k, A w i k * B w k j) z
  apply Finset.analyticAt_fun_sum
  intro k _
  exact (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hA i) k).mul
    (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hB k) j)

theorem fiber_analyticAt (material : Cell20 → ℝ) (z : ComplexMomentum) :
    AnalyticAt ℂ (fiber material) z :=
  (matrixProduct_analyticAt formalAdjointCurl curl z
    (formalAdjointCurl_analyticAt z) (curl_analyticAt z)).sub analyticAt_const

theorem curl_real (q : Momentum) : curl (realMomentum q) = PeriodicYee.curl q := rfl

theorem boundaryPhase_conjugate (q : Momentum) (j : Direction) (r : Cell20) :
    boundaryPhase (-realMomentum q) j r = star (boundaryPhase (realMomentum q) j r) := by
  unfold boundaryPhase
  split_ifs
  · rw [show star (Complex.exp (Complex.I * realMomentum q j)) =
      Complex.exp (star (Complex.I * realMomentum q j)) by exact (Complex.exp_conj _).symm]
    simp [realMomentum]
  · simp

theorem difference_conjugate (q : Momentum) (j : Direction) (r s : Cell20) :
    difference (-realMomentum q) j r s = star (difference (realMomentum q) j r s) := by
  unfold difference
  split_ifs <;> simp [boundaryPhase_conjugate]

theorem formalAdjointCurl_real (q : Momentum) :
    formalAdjointCurl (realMomentum q) = (PeriodicYee.curl q).conjTranspose := by
  ext i j
  change curl (-realMomentum q) j i = star (curl (realMomentum q) j i)
  unfold curl
  split_ifs <;> simp [difference_conjugate]

theorem fiber_real (material : Cell20 → ℝ) (q : Momentum) :
    fiber material (realMomentum q) = PeriodicYee.fiber material q := by
  unfold fiber PeriodicYee.fiber
  rw [curl_real, formalAdjointCurl_real]

def euclideanMap : Matrix Electric20 Electric20 ℂ →L[ℂ]
    (EuclideanSpace ℂ Electric20 →L[ℂ] EuclideanSpace ℂ Electric20) :=
  (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

def operator (material : Cell20 → ℝ) (z : ComplexMomentum) :
    EuclideanSpace ℂ Electric20 →L[ℂ] EuclideanSpace ℂ Electric20 :=
  euclideanMap (fiber material z)

theorem operator_analyticAt (material : Cell20 → ℝ) (z : ComplexMomentum) :
    AnalyticAt ℂ (operator material) z :=
  (euclideanMap.analyticAt _).comp (fiber_analyticAt material z)

theorem operator_real (material : Cell20 → ℝ) (q : Momentum) :
    operator material (realMomentum q) = Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber material q) := by
  unfold operator
  rw [fiber_real]
  rfl

end
end Maxwell.Spectral.ConventionalAnalytic
