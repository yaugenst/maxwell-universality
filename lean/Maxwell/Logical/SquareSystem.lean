import Maxwell.Logical.CircuitMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Maxwell.Logical.Circuit

theorem residual_noninput {n d : ℕ} (c : Circuit n d) (input : Fin n → ℝ)
    (state : Fin d → ℝ) (i : Fin d) (hi : n ≤ i.val) :
    c.residual input state i = c.residual 0 state i := by
  induction c with
  | input => exact False.elim (Nat.not_lt_of_ge hi i.isLt)
  | @append d c a ih =>
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro _; simp [residual]
      · intro hj
        simp only [residual, Fin.snoc_castSucc]
        exact ih (fun k => state k.castSucc) j hj

def originalInput {n d : ℕ} (c : Circuit n d) (state : Fin d → ℝ) : Fin n → ℝ :=
  fun i => state (c.inputIndex i)

/-- Replace the input boundary equations of the computed DAG by its actual
output equations. This is the square source-system encoding, before
symmetrization. -/
def squareMap {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun state i := if hi : i.val < n then state (output ⟨i.val, hi⟩) else c.equationMap state i
  map_add' a b := by
    funext i
    by_cases h : i.val < n <;> simp [h, map_add]
  map_smul' a b := by
    funext i
    by_cases h : i.val < n <;> simp [h, map_smul]

theorem squareMap_input {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d)
    (state : Fin d → ℝ) (i : Fin n) :
    c.squareMap output state (c.inputIndex i) = state (output i) := by
  simp only [squareMap, LinearMap.coe_mk, AddHom.coe_mk, c.inputIndex_value, i.isLt, dite_true]

theorem squareMap_noninput {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d)
    (state : Fin d → ℝ) (i : Fin d) (hi : n ≤ i.val) :
    c.squareMap output state i = c.residual 0 state i := by
  simp [squareMap, Nat.not_lt_of_ge hi, equationMap]

/-- Source invertibility yields square-circuit invertibility by the actual
forward interpreter. Only the verified zero-error output semantics are used. -/
theorem squareMap_injective {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hF : Function.Injective F)
    (hsem : ∀ input i, c.evaluate input 0 (output i) = F input i) :
    Function.Injective (c.squareMap output) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro state hzero
  have hgate : c.residual (c.originalInput state) state = 0 := by
    funext i
    by_cases hi : i.val < n
    · let j : Fin n := ⟨i.val, hi⟩
      have hij : c.inputIndex j = i := by
        apply Fin.ext
        exact c.inputIndex_value j
      rw [← hij, c.residual_at_input]
      simp [originalInput]
    · have hn : n ≤ i.val := Nat.le_of_not_gt hi
      rw [c.residual_noninput _ _ _ hn]
      have h := congrFun hzero i
      rw [c.squareMap_noninput output state i hn] at h
      exact h
  have hstate : state = c.evaluate (c.originalInput state) 0 := by
    rw [← hgate]
    exact (c.evaluate_residual (c.originalInput state) state).symm
  have hinput : c.originalInput state = 0 := by
    apply hF
    rw [map_zero]
    funext i
    have h := congrFun hzero (c.inputIndex i)
    rw [c.squareMap_input] at h
    rw [hstate, hsem] at h
    exact h
  rw [hstate, hinput, c.evaluate_zero]

noncomputable def squareEquiv {n d : ℕ} (c : Circuit n d) (output : Fin n → Fin d)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hF : Function.Injective F)
    (hsem : ∀ input i, c.evaluate input 0 (output i) = F input i) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearEquiv.ofInjectiveEndo (c.squareMap output) (c.squareMap_injective output F hF hsem)

end Maxwell.Logical.Circuit
