import Maxwell.Logical.SourceCircuit
import Maxwell.Logical.SourceRounding
import Maxwell.Logical.SquareSystem

namespace Maxwell.Logical

def roundedFunctionMap (S : Source.SparseSystem) (precision : ℕ) :
    (Fin S.n → ℝ) →ₗ[ℝ] (Fin S.n → ℝ) where
  toFun := roundedProduct S precision
  map_add' x y := by
    funext i
    simp [roundedProduct, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i
    simp [roundedProduct, Finset.mul_sum, mul_left_comm]

theorem roundedFunctionMap_injective (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) (precision : ℕ)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    Function.Injective (roundedFunctionMap S precision) := by
  obtain ⟨u, hu, _⟩ := Normalization.roundedOperator_unit S hunit hm precision hsmall
  intro x y hxy
  have he : (u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))
      (WithLp.toLp 2 x) =
      (u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) (WithLp.toLp 2 y) := by
    rw [hu]
    ext i
    exact congrFun hxy i
  have h := (ContinuousLinearEquiv.ofUnit u).injective he
  exact congrArg WithLp.ofLp h

def sourceSquareMap (S : Source.SparseSystem) (precision : ℕ) :
    (Fin (sourceCircuit S precision).size → ℝ) →ₗ[ℝ]
      (Fin (sourceCircuit S precision).size → ℝ) :=
  (sourceCircuit S precision).circuit.squareMap (sourceOutput S precision)

theorem sourceSquareMap_injective (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    Function.Injective (sourceSquareMap S precision) :=
  (sourceCircuit S precision).circuit.squareMap_injective (sourceOutput S precision)
    (roundedFunctionMap S precision)
    (roundedFunctionMap_injective S hunit (by omega) precision hsmall)
    (fun input i => sourceOutput_correct S hm precision hs input i)

/-- A linear equivalence for the actual square circuit constructed from the
sparse rational source. Its inverse is an analytic proof object; no inverse
matrix is computed or stored by the forward encoder. -/
noncomputable def sourceSquareEquiv (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    (Fin (sourceCircuit S precision).size → ℝ) ≃ₗ[ℝ]
      (Fin (sourceCircuit S precision).size → ℝ) :=
  LinearEquiv.ofInjectiveEndo (sourceSquareMap S precision)
    (sourceSquareMap_injective S hunit hm precision hs hsmall)

end Maxwell.Logical
