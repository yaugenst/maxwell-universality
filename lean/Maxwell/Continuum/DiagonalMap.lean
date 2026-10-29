import Maxwell.Continuum.WeakCurl

/-! Applying one bounded map to each of the three polarization components,
with its unchanged operator norm bound. -/

noncomputable section

namespace Maxwell.Continuum.DiagonalMap

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

abbrev Vector (A : Type*) := PiLp 2 (fun _ : Fin 3 => A)

def diagonal (T : A →L[ℂ] A) : Vector A →L[ℂ] Vector A :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => A)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => T.comp (PiLp.proj 2 (fun _ : Fin 3 => A) j)))

theorem diagonal_apply (T : A →L[ℂ] A) (u : Vector A) (j : Fin 3) : diagonal T u j = T (u j) := rfl

theorem diagonal_bound (T : A →L[ℂ] A) (u : Vector A) : ‖diagonal T u‖ ≤ ‖T‖ * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (u j)) 2

theorem diagonal_norm_le (T : A →L[ℂ] A) : ‖diagonal T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (diagonal_bound T)

def diagonalLinear : (A →L[ℂ] A) →ₗ[ℂ] (Vector A →L[ℂ] Vector A) where
  toFun := diagonal
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro u
    apply PiLp.ext
    intro j
    rfl
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro u
    apply PiLp.ext
    intro j
    rfl

def diagonalCLM : (A →L[ℂ] A) →L[ℂ] (Vector A →L[ℂ] Vector A) :=
  diagonalLinear.mkContinuous 1 (fun T => by
    change ‖diagonal T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using diagonal_norm_le T)

theorem diagonalCLM_apply (T : A →L[ℂ] A) : diagonalCLM T = diagonal T := rfl

end Maxwell.Continuum.DiagonalMap
