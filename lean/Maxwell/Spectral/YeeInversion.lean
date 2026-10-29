import Maxwell.Spectral.YeeTaylor
import Maxwell.Spectral.ConcreteSymmetry
import Maxwell.Spectral.CurlNorm
import Maxwell.Spectral.YeeTaylorConvolution
import Maxwell.Spectral.TaylorRemainder

/-! Spatial inversion of the actual primitive Yee stencil at time-reversal
momenta, including the phases from primitive-cell reduction. -/
namespace Maxwell.Spectral.YeeInversion

open Matrix
open Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor
open scoped Classical Matrix.Norms.L2Operator

noncomputable section

theorem latticeVector_neg (n : Translation) : latticeVector (-n) = -latticeVector n := by
  funext j
  fin_cases j <;> simp [latticeVector]
  ring

theorem character_neg_trim (k n : Translation) :
    character (timeReversalMomentum k) (-n) = character (timeReversalMomentum k) n := by
  rw [← character_conj, character_timeReversal]
  simp

/-- Reflect a scalar component at the physical stagger offset `t`. -/
def reflectRaw (t : RawCell) (p : Cell) : RawCell := -representative p - t

def reflectCell (t : RawCell) (p : Cell) : Cell := reduceCell (reflectRaw t p)

theorem reflectCell_involutive (t : RawCell) : Function.Involutive (reflectCell t) := by
  intro p
  have hr := reconstruct_reduce (reflectRaw t p)
  have he : reflectRaw t (reflectCell t p) =
      representative p + latticeVector (reduceTranslation (reflectRaw t p)) := by
    dsimp [reconstruct, reflectRaw, reflectCell] at hr ⊢
    calc
      _ = -(representative (reduceCell (-representative p - t)) +
          latticeVector (reduceTranslation (-representative p - t))) +
          latticeVector (reduceTranslation (-representative p - t)) - t := by abel
      _ = _ := by rw [hr]; abel
  rw [reflectCell, he, reduceCell_translate, reduceCell_representative]

theorem reflectCell_injective (t : RawCell) : Function.Injective (reflectCell t) :=
  (reflectCell_involutive t).injective

/-- This matrix includes the actual primitive boundary character. -/
def reflection (k : Momentum) (t : RawCell) : Matrix Cell Cell ℂ := fun p q =>
  if q = reflectCell t p then character k (reduceTranslation (reflectRaw t p)) else 0

theorem reflection_mulVec (k : Momentum) (t : RawCell) (v : Cell → ℂ) (p : Cell) :
    (reflection k t *ᵥ v) p = extend k v (reflectRaw t p) := by
  classical
  change (∑ q, (if q = reflectCell t p then
    character k (reduceTranslation (reflectRaw t p)) else 0) * v q) = _
  rw [Finset.sum_eq_single (reflectCell t p)]
  · simp [extend, reflectCell]
  · intro q _ hq
    simp [hq]
  · simp

theorem extend_reflection (k : Translation) (t : RawCell) (v : Cell → ℂ) (r : RawCell) :
    extend (timeReversalMomentum k) (reflection (timeReversalMomentum k) t *ᵥ v) r =
      extend (timeReversalMomentum k) v (-r - t) := by
  let p := reduceCell r
  let n := reduceTranslation r
  have hr : r = reconstruct p n := (reconstruct_reduce r).symm
  have he : -reconstruct p n - t = reflectRaw t p + latticeVector (-n) := by
    rw [latticeVector_neg]
    simp only [reconstruct, reflectRaw]
    abel
  rw [hr, he, extend_translate, character_neg_trim]
  simp only [extend, reduceTranslation_reconstruct, reduceCell_reconstruct, reflection_mulVec]

theorem reflection_sq (k : Translation) (t : RawCell) :
    reflection (timeReversalMomentum k) t * reflection (timeReversalMomentum k) t = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext p
  rw [← Matrix.mulVec_mulVec, reflection_mulVec, extend_reflection]
  have he : -reflectRaw t p - t = representative p := by unfold reflectRaw; abel
  rw [he, extend_representative, Matrix.one_mulVec]

theorem reflection_mul_conjTranspose (k : Momentum) (t : RawCell) :
    reflection k t * (reflection k t).conjTranspose = 1 := by
  ext p q
  by_cases hpq : p = q
  · subst q
    have hu : character k (reduceTranslation (reflectRaw t p)) *
        star (character k (reduceTranslation (reflectRaw t p))) = 1 := by
      rw [mul_comm]
      exact character_unit k _
    simpa [reflection, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul] using hu
  · have hf : reflectCell t p ≠ reflectCell t q := fun h => hpq (reflectCell_injective t h)
    simp [reflection, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, hf, hpq]

theorem reflection_conjTranspose (k : Translation) (t : RawCell) :
    (reflection (timeReversalMomentum k) t).conjTranspose =
      reflection (timeReversalMomentum k) t := by
  have hs := reflection_sq k t
  have hu := reflection_mul_conjTranspose (timeReversalMomentum k) t
  calc
    _ = 1 * (reflection (timeReversalMomentum k) t).conjTranspose := (one_mul _).symm
    _ = (reflection (timeReversalMomentum k) t * reflection (timeReversalMomentum k) t) *
        (reflection (timeReversalMomentum k) t).conjTranspose := by rw [hs]
    _ = _ := by rw [mul_assoc, hu, mul_one]

/-- Reflection reverses the actual boundary-phased primitive forward shift. -/
theorem shift_reflection (k : Translation) (t : RawCell) (j : Direction) :
    PrimitiveYee.shift (timeReversalMomentum k) j * reflection (timeReversalMomentum k) t =
      reflection (timeReversalMomentum k) (t + rawUnit j) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext p
  rw [← Matrix.mulVec_mulVec, reflection_mulVec]
  have h := extend_shift (timeReversalMomentum k) j
    (reflection (timeReversalMomentum k) t *ᵥ v) (representative p)
  rw [extend_representative, extend_reflection] at h
  rw [h]
  congr 1
  unfold reflectRaw
  abel

theorem reflection_shift (k : Momentum) (t : RawCell) (j : Direction) :
    reflection k (t + rawUnit j) * PrimitiveYee.shift k j = reflection k t := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext p
  rw [← Matrix.mulVec_mulVec, reflection_mulVec, reflection_mulVec, extend_shift]
  congr 1
  unfold reflectRaw
  abel

/-- Exact coefficient parity of the actual centered directional difference,
with the stagger correction provided by spatial reflection. -/
theorem differenceCoefficient_reflection (k : Translation) (q : Momentum)
    (n : ℕ) (t : RawCell) (j : Direction) :
    differenceCoefficient (timeReversalMomentum k) q n j *
        (-reflection (timeReversalMomentum k) t) =
      ((-1 : ℂ) ^ n) • (reflection (timeReversalMomentum k) (t + rawUnit j) *
        differenceCoefficient (timeReversalMomentum k) q n j) := by
  have hs : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]
    simp
  have hc : (-Complex.I * (theta * q j : ℝ)) ^ n / (n.factorial : ℂ) =
      (-1 : ℂ) ^ n * ((Complex.I * (theta * q j : ℝ)) ^ n / (n.factorial : ℂ)) := by
    rw [neg_mul, neg_pow]
    ring
  unfold differenceCoefficient
  rw [Matrix.mul_neg, sub_mul, smul_mul, smul_mul, shift_reflection, one_mul,
    mul_sub, Matrix.mul_smul, Matrix.mul_smul, reflection_shift, mul_one, hc]
  simp only [smul_sub, smul_smul, ← mul_assoc, hs, one_mul, neg_sub]

/-- A componentwise scalar matrix, in the physical `Direction × Cell` order. -/
def componentBlock (D : Direction → Matrix Cell Cell ℂ) : Matrix Electric Electric ℂ :=
  fun i j => if i.1 = j.1 then D i.1 i.2 j.2 else 0

theorem componentBlock_mul (D E : Direction → Matrix Cell Cell ℂ) :
    componentBlock D * componentBlock E = componentBlock (fun j => D j * E j) := by
  ext ⟨i, p⟩ ⟨j, q⟩
  fin_cases i <;> fin_cases j <;>
    simp [componentBlock, Matrix.mul_apply, Fintype.sum_prod_type]

theorem componentBlock_one : componentBlock (fun _ => (1 : Matrix Cell Cell ℂ)) = 1 := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [componentBlock, Matrix.one_apply, Prod.mk.injEq, ite_and]

theorem componentBlock_conjTranspose (D : Direction → Matrix Cell Cell ℂ) :
    (componentBlock D).conjTranspose = componentBlock (fun j => (D j).conjTranspose) := by
  ext ⟨i, p⟩ ⟨j, q⟩
  by_cases hij : i = j
  · subst j
    simp [componentBlock, Matrix.conjTranspose_apply]
  · simp [componentBlock, Matrix.conjTranspose_apply, hij, Ne.symm hij]

theorem mul_componentBlock_apply (A : Matrix Electric Electric ℂ)
    (D : Direction → Matrix Cell Cell ℂ) (i j : Direction) (p q : Cell) :
    (A * componentBlock D) (i, p) (j, q) =
      ((A.submatrix (fun r => (i, r)) (fun r => (j, r))) * D j) p q := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, componentBlock, Matrix.submatrix]

theorem componentBlock_mul_apply (D : Direction → Matrix Cell Cell ℂ)
    (A : Matrix Electric Electric ℂ) (i j : Direction) (p q : Cell) :
    (componentBlock D * A) (i, p) (j, q) =
      (D i * (A.submatrix (fun r => (i, r)) (fun r => (j, r)))) p q := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, componentBlock, Matrix.submatrix]

def faceOffset (d : Direction) : RawCell :=
  rawUnit (transverseDirections d).1 + rawUnit (transverseDirections d).2

/-- Electric vectors are polar, and their physical edge offset is one half-cell
in their own direction. -/
def electricInversion (k : Translation) : Matrix Electric Electric ℂ :=
  componentBlock fun j => -reflection (timeReversalMomentum k) (rawUnit j)

/-- Face vectors are axial, with the two transverse half-cell offsets. -/
def faceInversion (k : Translation) : Matrix Face Face ℂ :=
  componentBlock fun j => reflection (timeReversalMomentum k) (faceOffset j)

theorem electricInversion_sq (k : Translation) : electricInversion k * electricInversion k = 1 := by
  rw [electricInversion, componentBlock_mul]
  simp only [neg_mul_neg, reflection_sq]
  exact componentBlock_one

theorem faceInversion_sq (k : Translation) : faceInversion k * faceInversion k = 1 := by
  rw [faceInversion, componentBlock_mul]
  simp only [reflection_sq]
  exact componentBlock_one

theorem electricInversion_conjTranspose (k : Translation) :
    (electricInversion k).conjTranspose = electricInversion k := by
  simp only [electricInversion, componentBlock_conjTranspose, Matrix.conjTranspose_neg,
    reflection_conjTranspose]

theorem faceInversion_conjTranspose (k : Translation) :
    (faceInversion k).conjTranspose = faceInversion k := by
  simp only [faceInversion, componentBlock_conjTranspose, reflection_conjTranspose]

/-- The exact parity relation for the three-component primitive curl. -/
theorem curlCoefficient_reflection (k : Translation) (q : Momentum) (n : ℕ) :
    Maxwell.Spectral.curlBlock (differenceCoefficient (timeReversalMomentum k) q n) *
        electricInversion k =
      ((-1 : ℂ) ^ n) • (faceInversion k *
        Maxwell.Spectral.curlBlock (differenceCoefficient (timeReversalMomentum k) q n)) := by
  have h := differenceCoefficient_reflection k q n
  ext ⟨i, p⟩ ⟨j, r⟩
  simp only [electricInversion, faceInversion, Matrix.smul_apply, smul_eq_mul,
    mul_componentBlock_apply, componentBlock_mul_apply]
  fin_cases i <;> fin_cases j
  all_goals simp only [Maxwell.Spectral.curlBlock, Matrix.submatrix,
    faceOffset, transverseDirections, Fin.isValue]
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (faceOffset 0) *
        (0 : Matrix Cell Cell ℂ)) p r
    simp
  · change ((-differenceCoefficient (timeReversalMomentum k) q n 2) *
        (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 1 + rawUnit 2) *
        (-differenceCoefficient (timeReversalMomentum k) q n 2)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, neg_neg,
      Matrix.smul_apply, smul_eq_mul, mul_neg] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 1) 2)
  · change (differenceCoefficient (timeReversalMomentum k) q n 1 *
        (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 1 + rawUnit 2) *
        differenceCoefficient (timeReversalMomentum k) q n 1) p r
    simpa only [Matrix.smul_apply, smul_eq_mul, add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 2) 1)
  · change (differenceCoefficient (timeReversalMomentum k) q n 2 *
        (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 2) *
        differenceCoefficient (timeReversalMomentum k) q n 2) p r
    exact congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 0) 2)
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (faceOffset 1) *
        (0 : Matrix Cell Cell ℂ)) p r
    simp
  · change ((-differenceCoefficient (timeReversalMomentum k) q n 0) *
        (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 2) *
        (-differenceCoefficient (timeReversalMomentum k) q n 0)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, neg_neg,
      Matrix.smul_apply, smul_eq_mul, mul_neg, add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 2) 0)
  · change ((-differenceCoefficient (timeReversalMomentum k) q n 1) *
        (-reflection (timeReversalMomentum k) (rawUnit 0))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 1) *
        (-differenceCoefficient (timeReversalMomentum k) q n 1)) p r
    simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, neg_neg,
      Matrix.smul_apply, smul_eq_mul, mul_neg] using
      congrArg (fun M : Matrix Cell Cell ℂ => -M p r) (h (rawUnit 0) 1)
  · change (differenceCoefficient (timeReversalMomentum k) q n 0 *
        (-reflection (timeReversalMomentum k) (rawUnit 1))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (rawUnit 0 + rawUnit 1) *
        differenceCoefficient (timeReversalMomentum k) q n 0) p r
    simpa only [Matrix.smul_apply, smul_eq_mul, add_comm] using
      congrArg (fun M : Matrix Cell Cell ℂ => M p r) (h (rawUnit 1) 0)
  · change ((0 : Matrix Cell Cell ℂ) * (-reflection (timeReversalMomentum k) (rawUnit 2))) p r =
      (-1 : ℂ)^n * (reflection (timeReversalMomentum k) (faceOffset 2) *
        (0 : Matrix Cell Cell ℂ)) p r
    simp

/-- Conjugation of each curl coefficient propagates through its genuine Cauchy
product.  No parity hypothesis on the Maxwell coefficients is required. -/
theorem coefficient_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ → Matrix ι ι ℂ) (E F : Matrix ι ι ℂ)
    (hE : E.conjTranspose = E) (hF : F.conjTranspose = F) (hFsq : F * F = 1)
    (hC : ∀ n, C n * E = ((-1 : ℂ)^n) • (F * C n)) (n : ℕ) :
    E * YeeTaylorConvolution.coefficient C n * E =
      ((-1 : ℂ)^n) • YeeTaylorConvolution.coefficient C n := by
  unfold YeeTaylorConvolution.coefficient
  rw [Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hleft := congrArg Matrix.conjTranspose (hC p.1)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    hE, hF, star_pow, star_neg, star_one] at hleft
  change E * ((C p.1).conjTranspose * C p.2) * E = _
  calc
    _ = (E * (C p.1).conjTranspose) * (C p.2 * E) := by simp only [mul_assoc]
    _ = (((-1 : ℂ)^p.1) • ((C p.1).conjTranspose * F)) *
        (((-1 : ℂ)^p.2) • (F * C p.2)) := by rw [hleft, hC]
    _ = (((-1 : ℂ)^p.1) * ((-1 : ℂ)^p.2)) •
        ((C p.1).conjTranspose * (F * F) * C p.2) := by
      simp only [smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
      congr 1
      exact mul_comm _ _
    _ = _ := by rw [hFsq, mul_one, ← pow_add, he]; rfl

/-- The actual frozen edge-averaged dielectric commutes with physical inversion. -/
theorem mass_commutes (k : Translation) :
    electricInversion k * PrimitiveYee.mass Concrete.material =
      PrimitiveYee.mass Concrete.material * electricInversion k := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [PrimitiveYee.mass, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    by_cases hq : q = reflectCell (rawUnit i) p
    · subst q
      have hm := Concrete.primitiveEdgeAverage_inversion i p
      change PrimitiveYee.edgeAverage Concrete.material (i, reflectCell (rawUnit i) p) =
        PrimitiveYee.edgeAverage Concrete.material (i, p) at hm
      simp only [hm, electricInversion, componentBlock, ↓reduceIte,
        Matrix.neg_apply, reflection]
      ring
    · simp [electricInversion, componentBlock, reflection, hq]
  · simp [electricInversion, componentBlock, hij]

theorem mass_conjugation (k : Translation) :
    electricInversion k * PrimitiveYee.mass Concrete.material * electricInversion k =
      PrimitiveYee.mass Concrete.material := by
  rw [mass_commutes, mul_assoc, electricInversion_sq, mul_one]

/-- Every coefficient of the actual primitive curl-curl series has exact
inversion parity at every primitive time-reversal momentum. -/
theorem laplacianCoefficient_conjugation (k : Translation) (q : Momentum) (n : ℕ) :
    electricInversion k *
        YeeTaylorConvolution.coefficient (curlCoefficient (timeReversalMomentum k) q) n *
          electricInversion k =
      ((-1 : ℂ)^n) •
        YeeTaylorConvolution.coefficient (curlCoefficient (timeReversalMomentum k) q) n := by
  apply coefficient_conjugation _ _ (faceInversion k)
    (electricInversion_conjTranspose k) (faceInversion_conjTranspose k) (faceInversion_sq k)
  intro m
  exact curlCoefficient_reflection k q m

/-- The full frozen Maxwell coefficient parity includes its actual material. -/
theorem fiberCoefficient_conjugation (k : Translation) (q : Momentum) (n : ℕ) :
    electricInversion k * fiberCoefficient Concrete.material (timeReversalMomentum k) q n *
        electricInversion k =
      ((-1 : ℂ)^n) • fiberCoefficient Concrete.material (timeReversalMomentum k) q n := by
  unfold fiberCoefficient
  rw [mul_sub, sub_mul, laplacianCoefficient_conjugation]
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte, pow_zero, one_smul, Matrix.mul_smul, smul_mul,
      mass_conjugation]
  · simp [hn]

/-- Matrix form of the Taylor parity relation used by the residual theorems. -/
theorem fiberCoefficient_parity (k : Translation) (q : Momentum) (n : ℕ) :
    electricInversion k * fiberCoefficient Concrete.material (timeReversalMomentum k) q n =
      ((-1 : ℂ)^n) •
        (fiberCoefficient Concrete.material (timeReversalMomentum k) q n * electricInversion k) := by
  have h := congrArg (fun M : Matrix Electric Electric ℂ => M * electricInversion k)
    (fiberCoefficient_conjugation k q n)
  simpa only [mul_assoc, electricInversion_sq, mul_one, smul_mul] using h

/-- The actual electric reflection as a unitary operator on the Euclidean
primitive-cell field space. -/
def electricUnitary (k : Translation) :
    unitary (EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric) :=
  ⟨Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricInversion k), by
    let T := Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    have hs : star (T (electricInversion k)) = T (electricInversion k) := by
      rw [← map_star]
      exact congrArg T (electricInversion_conjTranspose k)
    have hm : T (electricInversion k) * T (electricInversion k) = 1 := by
      rw [← map_mul, electricInversion_sq, map_one]
    change star (T (electricInversion k)) * T (electricInversion k) = 1 ∧
      T (electricInversion k) * star (T (electricInversion k)) = 1
    rw [hs]
    exact ⟨hm, hm⟩⟩

def electricIsometry (k : Translation) :
    EuclideanSpace ℂ Electric ≃ₗᵢ[ℂ] EuclideanSpace ℂ Electric :=
  Unitary.linearIsometryEquiv (electricUnitary k)

theorem electricIsometry_apply (k : Translation) (v : EuclideanSpace ℂ Electric) :
    electricIsometry k v =
      Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricInversion k) v := rfl

theorem electricIsometry_involutive (k : Translation) :
    Function.Involutive (electricIsometry k) := by
  intro v
  simp only [electricIsometry_apply]
  have h := congrArg (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)) (electricInversion_sq k)
  have hv := congrArg (fun L : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric => L v) h
  simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using hv

/-- Matrix coefficient parity passes exactly to the Euclidean operator family. -/
theorem matrixParity_to_TaylorParity (k : Translation) (A : ℕ → Matrix Electric Electric ℂ)
    (hA : ∀ n, electricInversion k * A n = ((-1 : ℂ)^n) • (A n * electricInversion k)) :
    Maxwell.Spectral.TaylorParity (electricIsometry k)
      (fun n => Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (A n)) := by
  intro n v
  have h := congrArg (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)) (hA n)
  have hv := congrArg (fun L : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric => L v) h
  simpa only [electricIsometry_apply, map_mul, map_smul,
    mul_apply_eq_comp, _root_.smul_apply] using hv

theorem fiberOperator_taylorParity (k : Translation) (q : Momentum) :
    Maxwell.Spectral.TaylorParity (electricIsometry k)
      (fun n => Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (fiberCoefficient Concrete.material (timeReversalMomentum k) q n)) :=
  matrixParity_to_TaylorParity k _ (fiberCoefficient_parity k q)

theorem shiftedFiberCoefficient_parity (k : Translation) (q : Momentum) (E : ℝ) (n : ℕ) :
    electricInversion k * shiftedFiberCoefficient Concrete.material (timeReversalMomentum k) q E n =
      ((-1 : ℂ)^n) •
        (shiftedFiberCoefficient Concrete.material (timeReversalMomentum k) q E n *
          electricInversion k) := by
  unfold shiftedFiberCoefficient
  rw [mul_sub, sub_mul, fiberCoefficient_parity]
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte, pow_zero, one_smul, Matrix.mul_smul, smul_mul, mul_one, one_mul]
  · simp [hn]

/-- The exact public premise of the Taylor residual and compression bounds,
discharged for the frozen primitive Yee operator and every real spectral shift. -/
theorem shiftedOperator_taylorParity (k : Translation) (q : Momentum) (E : ℝ) :
    Maxwell.Spectral.TaylorParity (electricIsometry k)
      (shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q E) :=
  matrixParity_to_TaylorParity k _ (shiftedFiberCoefficient_parity k q E)


end
end Maxwell.Spectral.YeeInversion
