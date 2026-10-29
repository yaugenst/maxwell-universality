import Maxwell.Spectral.YeeAnalytic
import Maxwell.Spectral.YeeInversion

/-! Algebraic inversion covariance of the actual holomorphic primitive Yee
family.  The complex momentum is negated without using a real-locus identity
theorem or assuming covariance of the continued operator. -/
namespace Maxwell.Spectral.YeeAnalyticInversion

open Matrix
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor Maxwell.Spectral.YeeInversion
open Maxwell.Spectral.YeeAnalytic
open scoped Classical Matrix.Norms.L2Operator

noncomputable section

def holomorphicDifference (k : Momentum) (z : ComplexMomentum) (j : Direction) :
    Matrix Cell Cell ℂ :=
  Complex.exp ((Complex.I * (theta : ℂ)) * z j) • PrimitiveYee.shift k j -
    Complex.exp (-(Complex.I * (theta : ℂ)) * z j) • (1 : Matrix Cell Cell ℂ)

theorem holomorphicCurl_eq_curlBlock (k : Momentum) (z : ComplexMomentum) :
    holomorphicCurl k z = curlBlock (holomorphicDifference k z) := by
  ext ⟨i, p⟩ ⟨j, r⟩
  fin_cases i <;> fin_cases j <;>
    simp [holomorphicCurl, exponentialStencil, shiftCurl, identityCurl,
      holomorphicDifference, curlBlock, Fin.sum_univ_three]
  all_goals ring

theorem holomorphicDifference_reflection (k : Translation) (z : ComplexMomentum)
    (t : RawCell) (j : Direction) :
    holomorphicDifference (timeReversalMomentum k) z j *
        (-reflection (timeReversalMomentum k) t) =
      reflection (timeReversalMomentum k) (t + rawUnit j) *
        holomorphicDifference (timeReversalMomentum k) (-z) j := by
  unfold holomorphicDifference
  rw [Matrix.mul_neg, sub_mul, smul_mul, smul_mul, shift_reflection, one_mul,
    mul_sub, Matrix.mul_smul, Matrix.mul_smul, reflection_shift, mul_one]
  simp only [Pi.neg_apply, mul_neg, neg_mul, neg_neg, neg_sub]

/-- Componentwise staggered reflection lifts exactly to the physical curl. -/
theorem curlBlock_reflection (k : Translation)
    (D G : Direction → Matrix Cell Cell ℂ)
    (h : ∀ t j, D j * (-reflection (timeReversalMomentum k) t) =
      reflection (timeReversalMomentum k) (t + rawUnit j) * G j) :
    curlBlock D * electricInversion k = faceInversion k * curlBlock G := by
  ext ⟨i, p⟩ ⟨j, r⟩
  simp only [electricInversion, faceInversion, mul_componentBlock_apply, componentBlock_mul_apply]
  fin_cases i <;> fin_cases j
  all_goals simp only [curlBlock, Matrix.submatrix, YeeInversion.faceOffset, transverseDirections, Fin.isValue]
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (reflection (timeReversalMomentum k) (YeeInversion.faceOffset 0) * (0 : Matrix Cell Cell ℂ)) p r
    simp
  · change ((-D 2) * (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 1 + rawUnit 2) * (-G 2)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 1) 2)
  · change (D 1 * (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 1 + rawUnit 2) * G 1) p r
    simpa only [add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 2) 1)
  · change (D 2 * (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 2) * G 2) p r
    exact congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 0) 2)
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (reflection (timeReversalMomentum k) (YeeInversion.faceOffset 1) * (0 : Matrix Cell Cell ℂ)) p r
    simp
  · change ((-D 0) * (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 2) * (-G 0)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 2) 0)
  · change ((-D 1) * (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 1) * (-G 1)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 0) 1)
  · change (D 0 * (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 1) * G 0) p r
    simpa only [add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 1) 0)
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (reflection (timeReversalMomentum k) (YeeInversion.faceOffset 2) * (0 : Matrix Cell Cell ℂ)) p r
    simp

/-- Exact inversion covariance of the holomorphic curl, including complex
Cartesian momentum and actual primitive boundary phases. -/
theorem holomorphicCurl_reflection (k : Translation) (z : ComplexMomentum) :
    holomorphicCurl (timeReversalMomentum k) z * electricInversion k =
      faceInversion k * holomorphicCurl (timeReversalMomentum k) (-z) := by
  rw [holomorphicCurl_eq_curlBlock, holomorphicCurl_eq_curlBlock]
  exact curlBlock_reflection k _ _ (holomorphicDifference_reflection k z)

/-- The formal adjoint is the adjoint of the curl at conjugate momentum. -/
theorem holomorphicCurlAdjoint_eq (k : Momentum) (z : ComplexMomentum) :
    holomorphicCurlAdjoint k z = (holomorphicCurl k (star z)).conjTranspose := by
  simp only [holomorphicCurl, holomorphicCurlAdjoint, exponentialStencil,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1 <;> congr 1
  · change _ = starRingEnd ℂ (Complex.exp _)
    rw [← Complex.exp_conj]
    simp
  · change _ = starRingEnd ℂ (Complex.exp _)
    rw [← Complex.exp_conj]
    simp

theorem holomorphicCurlAdjoint_reflection (k : Translation) (z : ComplexMomentum) :
    electricInversion k * holomorphicCurlAdjoint (timeReversalMomentum k) z =
      holomorphicCurlAdjoint (timeReversalMomentum k) (-z) * faceInversion k := by
  have h := congrArg Matrix.conjTranspose (holomorphicCurl_reflection k (star z))
  simpa only [Matrix.conjTranspose_mul, electricInversion_conjTranspose,
    faceInversion_conjTranspose, holomorphicCurlAdjoint_eq, star_neg] using h

/-- Inversion covariance of the actual complete holomorphic Maxwell matrix. -/
theorem holomorphicFiber_conjugation (k : Translation) (z : ComplexMomentum) :
    electricInversion k * holomorphicFiber Concrete.material (timeReversalMomentum k) z *
        electricInversion k =
      holomorphicFiber Concrete.material (timeReversalMomentum k) (-z) := by
  unfold holomorphicFiber
  rw [mul_sub, sub_mul, Matrix.mul_smul, smul_mul, mass_conjugation]
  congr 1
  calc
    _ = (electricInversion k * holomorphicCurlAdjoint (timeReversalMomentum k) z) *
        (holomorphicCurl (timeReversalMomentum k) z * electricInversion k) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [holomorphicCurlAdjoint_reflection, holomorphicCurl_reflection]
      simp only [mul_assoc, ← mul_assoc (faceInversion k), faceInversion_sq, one_mul]

/-- The public operator family has the same exact holomorphic inversion law. -/
theorem holomorphicOperator_reflection (k : Translation) (E : ℝ)
    (z : ComplexMomentum) (v : EuclideanSpace ℂ Electric) :
    electricIsometry k (holomorphicOperator Concrete.material (timeReversalMomentum k) E z v) =
      holomorphicOperator Concrete.material (timeReversalMomentum k) E (-z) (electricIsometry k v) := by
  have hm : electricInversion k *
      (holomorphicFiber Concrete.material (timeReversalMomentum k) z - (E : ℂ) • 1) =
      (holomorphicFiber Concrete.material (timeReversalMomentum k) (-z) - (E : ℂ) • 1) *
        electricInversion k := by
    have h := congrArg (fun M : Matrix Electric Electric ℂ => M * electricInversion k)
      (holomorphicFiber_conjugation k z)
    simp only [mul_assoc, electricInversion_sq, mul_one] at h
    simp only [mul_sub, sub_mul, Matrix.mul_smul, smul_mul, mul_one, one_mul, h]
  have h := congrArg (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)) hm
  have hv := congrArg (fun L : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric => L v) h
  simp only [map_mul, mul_apply_eq_comp] at hv
  exact hv

end
end Maxwell.Spectral.YeeAnalyticInversion
