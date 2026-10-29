import Maxwell.Certificate.PrimitiveBinding
import Maxwell.Spectral.YeeTaylorCoefficients

/-! Exact rational derivative stencils and their binding to the first two
Taylor coefficients of the actual primitive Maxwell fiber. -/
namespace Maxwell.Certificate.DerivativeBinding

open Matrix
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Cell20 Momentum)
open Maxwell.Spectral.YeeTaylor Maxwell.Spectral.YeeTaylorCoefficients
open Maxwell.Certificate.PrimitiveBinding
open scoped Classical Matrix.Norms.L2Operator

noncomputable section

def castQ {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℚ →+* Matrix ι ι ℂ := (Rat.castHom ℂ).mapMatrix

theorem castQ_transpose {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    castQ A.transpose = (castQ A).conjTranspose := by
  ext i j
  simp [castQ, RingHom.mapMatrix]

theorem castQ_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℚ) (A : Matrix ι ι ℚ) :
    castQ (r • A) = (r : ℂ) • castQ A := by
  ext i j
  simp [castQ, RingHom.mapMatrix]

def curlBlockQ (D : Direction → Matrix Cell Cell ℚ) : Matrix Electric Electric ℚ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then D 1 i.2 j.2 else if j.1 = 1 then -D 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then D 2 i.2 j.2 else if j.1 = 2 then -D 0 i.2 j.2 else 0
  else
    if j.1 = 1 then D 0 i.2 j.2 else if j.1 = 0 then -D 1 i.2 j.2 else 0

/-- Directional first-derivative curl with its common factor `iθ` removed. -/
def KQ (k : Translation) (i : Direction) : Matrix Electric Electric ℚ :=
  curlBlockQ (Pi.single i (differenceQ k i + (2 : ℚ) • 1))

/-- Directional second-derivative curl with its common factor `−θ²/2` removed. -/
def LQ (k : Translation) (i : Direction) : Matrix Electric Electric ℚ :=
  curlBlockQ (Pi.single i (differenceQ k i))

def BQ (k : Translation) (i : Direction) : Matrix Electric Electric ℚ :=
  (curlQ k).transpose * KQ k i - (KQ k i).transpose * curlQ k

def DQ (k : Translation) (i j : Direction) : Matrix Electric Electric ℚ :=
  (KQ k i).transpose * KQ k j + (KQ k j).transpose * KQ k i -
    if i = j then (LQ k i).transpose * curlQ k + (curlQ k).transpose * LQ k i else 0

theorem curlBlockQ_binding (D : Direction → Matrix Cell Cell ℚ) :
    castQ (curlBlockQ D) = curlBlock (fun j => castQ (D j)) := by
  ext i j
  simp only [castQ, RingHom.mapMatrix_apply, Matrix.map_apply, curlBlockQ, curlBlock]
  split_ifs <;> simp

theorem castQ_difference (k : Translation) (j : Direction) :
    castQ (differenceQ k j) = difference (timeReversalMomentum k) j :=
  difference_binding k j

theorem castQ_curl (k : Translation) :
    castQ (curlQ k) = PrimitiveYee.curl (timeReversalMomentum k) := curl_binding k

theorem KQ_binding (k : Translation) (i : Direction) :
    castQ (KQ k i) =
      curlBlock (Pi.single i (PrimitiveYee.shift (timeReversalMomentum k) i + 1)) := by
  rw [KQ, curlBlockQ_binding]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, map_add, castQ_smul, map_one, castQ_difference,
      difference_eq_shift_sub_one, Rat.cast_ofNat]
    module
  · simp [hji]

theorem LQ_binding (k : Translation) (i : Direction) :
    castQ (LQ k i) = curlBlock (Pi.single i (difference (timeReversalMomentum k) i)) := by
  rw [LQ, curlBlockQ_binding]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, castQ_difference]
  · simp [hji]

/-- Weighted rational first-derivative stencils give the actual first curl jet. -/
theorem firstCurl_binding (k : Translation) (q : Momentum) :
    firstCurl (timeReversalMomentum k) q = ∑ i : Direction, (q i : ℂ) • castQ (KQ k i) := by
  simp only [KQ_binding]
  ext ⟨i, p⟩ ⟨j, r⟩
  fin_cases i <;> fin_cases j <;>
    simp [firstCurl, curlBlock, Fin.sum_univ_three]
  all_goals ring

theorem secondCurl_binding (k : Translation) (q : Momentum) :
    secondCurl (timeReversalMomentum k) q = ∑ i : Direction, ((q i : ℂ)^2) • castQ (LQ k i) := by
  simp only [LQ_binding]
  ext ⟨i, p⟩ ⟨j, r⟩
  fin_cases i <;> fin_cases j <;>
    simp [secondCurl, curlBlock, Fin.sum_univ_three]

theorem BQ_binding (k : Translation) (i : Direction) :
    castQ (BQ k i) =
      (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * castQ (KQ k i) -
        (castQ (KQ k i)).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) := by
  simp only [BQ, map_sub, map_mul, castQ_transpose, castQ_curl]

theorem DQ_binding (k : Translation) (i j : Direction) :
    castQ (DQ k i j) =
      (castQ (KQ k i)).conjTranspose * castQ (KQ k j) +
        (castQ (KQ k j)).conjTranspose * castQ (KQ k i) -
        if i = j then
          (castQ (LQ k i)).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
            (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * castQ (LQ k i)
        else 0 := by
  by_cases hij : i = j <;>
    simp only [DQ, hij, ↓reduceIte, map_sub, map_add, map_mul, castQ_transpose, castQ_curl, map_zero]

theorem weighted_BQ (k : Translation) (q : Momentum) :
    (∑ i : Direction, (q i : ℂ) • castQ (BQ k i)) =
      (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * firstCurl (timeReversalMomentum k) q -
        (firstCurl (timeReversalMomentum k) q).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) := by
  have hs (i : Direction) : star (q i : ℂ) = (q i : ℂ) := by simp
  simp only [BQ_binding, smul_sub, Finset.sum_sub_distrib, firstCurl_binding,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hs,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul, Matrix.mul_smul]

/-- The first-order rational certificate combination is exactly the actual
homogeneous Maxwell coefficient, including its common imaginary scale. -/
theorem fiberCoefficient_one_binding (k : Translation) (q : Momentum) :
    fiberCoefficient Concrete.material (timeReversalMomentum k) q 1 =
      (Complex.I * (theta : ℂ)) • ∑ i : Direction, (q i : ℂ) • castQ (BQ k i) := by
  rw [fiberCoefficient_one_factored, weighted_BQ]

theorem firstCurl_gram_binding (k : Translation) (q : Momentum) :
    (firstCurl (timeReversalMomentum k) q).conjTranspose * firstCurl (timeReversalMomentum k) q =
      ∑ i : Direction, ∑ j : Direction,
        ((q i : ℂ) * (q j : ℂ)) • ((castQ (KQ k i)).conjTranspose * castQ (KQ k j)) := by
  have hs (i : Direction) : star (q i : ℂ) = (q i : ℂ) := by simp
  simp only [firstCurl_binding, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    hs, Matrix.sum_mul, Matrix.mul_sum, smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (q i : ℂ) (q j : ℂ)]

theorem secondCurl_mixed_binding (k : Translation) (q : Momentum) :
    (secondCurl (timeReversalMomentum k) q).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
        (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * secondCurl (timeReversalMomentum k) q =
      ∑ i : Direction, ((q i : ℂ)^2) •
        ((castQ (LQ k i)).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
          (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * castQ (LQ k i)) := by
  have hs (i : Direction) : star ((q i : ℂ)^2) = (q i : ℂ)^2 := by simp
  simp only [secondCurl_binding, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    hs, Matrix.sum_mul, Matrix.mul_sum, smul_mul, Matrix.mul_smul, smul_add, Finset.sum_add_distrib]

theorem weighted_DQ (k : Translation) (q : Momentum) :
    (∑ i : Direction, ∑ j : Direction, ((q i : ℂ) * (q j : ℂ)) • castQ (DQ k i j)) =
      (2 : ℂ) • ((firstCurl (timeReversalMomentum k) q).conjTranspose * firstCurl (timeReversalMomentum k) q) -
        ((secondCurl (timeReversalMomentum k) q).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
          (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * secondCurl (timeReversalMomentum k) q) := by
  have hswap : (∑ i : Direction, ∑ j : Direction,
      ((q i : ℂ) * (q j : ℂ)) • ((castQ (KQ k j)).conjTranspose * castQ (KQ k i))) =
      ∑ i : Direction, ∑ j : Direction,
        ((q i : ℂ) * (q j : ℂ)) • ((castQ (KQ k i)).conjTranspose * castQ (KQ k j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (q i : ℂ) (q j : ℂ)]
  have hdiag : (∑ i : Direction, ∑ j : Direction, ((q i : ℂ) * (q j : ℂ)) •
      (if i = j then
        (castQ (LQ k i)).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
          (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * castQ (LQ k i) else 0)) =
      (secondCurl (timeReversalMomentum k) q).conjTranspose * PrimitiveYee.curl (timeReversalMomentum k) +
        (PrimitiveYee.curl (timeReversalMomentum k)).conjTranspose * secondCurl (timeReversalMomentum k) q := by
    rw [secondCurl_mixed_binding]
    simp [smul_ite, pow_two]
  simp only [DQ_binding, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap, hdiag, ← firstCurl_gram_binding]
  module

/-- The rational Hessian combination is exactly the quadratic homogeneous
Maxwell coefficient, with the correct Taylor factor `θ²/2`. -/
theorem fiberCoefficient_two_binding (k : Translation) (q : Momentum) :
    fiberCoefficient Concrete.material (timeReversalMomentum k) q 2 =
      ((theta : ℂ)^2 / 2) •
        ∑ i : Direction, ∑ j : Direction, ((q i : ℂ) * (q j : ℂ)) • castQ (DQ k i j) := by
  rw [fiberCoefficient_two_factored, weighted_DQ]
  module

end
end Maxwell.Certificate.DerivativeBinding
