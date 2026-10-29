import Maxwell.Composition.PeriodicBackground
import Maxwell.Composition.ComplexInverse
import Maxwell.Probability.PhysicalShift

/-! A source-independent common event for the actual complete finite PEC
background matrix, with real and complex inverses and exact operator binding. -/
noncomputable section
namespace Maxwell.Composition.PhysicalBackground
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Probability
open scoped Matrix.Norms.L2Operator

variable (P : PhysicalPlatform) (box : Target.Box)

def material : ScalarMaterial box.nx box.ny box.nz where
  value c := P.background.material (siteMod20 (Target.latticeCell c))
  bounds c := by
    have h := P.background.bounds (siteMod20 (Target.latticeCell c))
    have hr := P.background.reserve_pos
    exact ⟨h.1, by linarith⟩

def matrix : Matrix box.Edge box.Edge ℝ := (Target.maxwell (material P box)).map Rat.cast

theorem matrix_hermitian : (matrix P box).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr ((Target.maxwell_symmetric (material P box)).map (fun q => (q : ℝ)))

def eigenvalues : Fin (Fintype.card box.Edge) → ℝ :=
  fun i => (matrix_hermitian P box).eigenvalues ((Fintype.equivFin box.Edge).symm i)

def bad (m J : ℕ) (τ : ℚ) : Finset ℕ :=
  spectralBad (eigenvalues P box) τ (detuningRadius m (Fintype.card box.Edge) τ) J

def shiftedMatrix (σ : ℚ) : Matrix box.Edge box.Edge ℝ := matrix P box - (σ : ℝ) • 1

theorem good_inverse (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :
    InverseBound (shiftedMatrix P box (rationalMidpoint τ J j.val))
      (inverseBudget m (Fintype.card box.Edge) τ) := by
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < inverseBudget m (Fintype.card box.Edge) τ := by
    dsimp [inverseBudget]; positivity
  unfold shiftedMatrix
  rw [rationalMidpoint_cast]
  apply shifted_inverseBound (matrix_hermitian P box) _ _ hL
  intro e
  by_contra hn
  apply hj
  apply (mem_spectralBad _ _ _ _ _).mpr
  refine ⟨j.isLt, ⟨(Fintype.equivFin box.Edge) e, ?_⟩⟩
  simpa only [eigenvalues, Equiv.symm_apply_apply,
    detuningRadius_eq_inverseBudget_inv] using (lt_of_not_ge hn)

theorem failure_probability (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (hgrid : 16 * (m + Fintype.card box.Edge)^2 ≤ J) :
    ∃ hJ : 0 < J, gridProbability J hJ (bad P box m J τ) ≤ 3 / (64 * (m : ℝ)) := by
  obtain ⟨hJ, hprob, hbound⟩ := finite_detuning_probability (eigenvalues P box) m J τ hm
    (by exact_mod_cast hτ) hgrid
  exact ⟨hJ, hprob.trans hbound⟩

def realEquiv (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :=
  ComplexInverse.realEquiv (shiftedMatrix P box (rationalMidpoint τ J j.val))
    (good_inverse P box m J τ hm hτ j hj)

def complexEquiv (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :=
  ComplexInverse.complexEquiv (shiftedMatrix P box (rationalMidpoint τ J j.val))
    (good_inverse P box m J τ hm hτ j hj)

theorem real_inverse_bound (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :
    ‖((realEquiv P box m J τ hm hτ j hj).symm : EuclideanSpace ℝ box.Edge →L[ℝ]
      EuclideanSpace ℝ box.Edge)‖ ≤ inverseBudget m (Fintype.card box.Edge) τ :=
  ComplexInverse.realEquiv_inverse_norm_le _ _

theorem complex_inverse_bound (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :
    ‖((complexEquiv P box m J τ hm hτ j hj).symm : EuclideanSpace ℂ box.Edge →L[ℂ]
      EuclideanSpace ℂ box.Edge)‖ ≤ inverseBudget m (Fintype.card box.Edge) τ :=
  ComplexInverse.complexEquiv_inverse_norm_le _ _

theorem shifted_complex_operator (σ : ℚ) :
    Matrix.toEuclideanCLM (n := box.Edge) (𝕜 := ℂ) ((shiftedMatrix P box σ).map Complex.ofReal) =
      Green.pecMaxwellOperator (material P box) - (σ : ℂ) • 1 := by
  have he : (shiftedMatrix P box σ).map Complex.ofReal =
      (Target.maxwell (material P box)).map (fun q => (q : ℂ)) - (σ : ℂ) • 1 := by
    ext e f
    simp [shiftedMatrix, matrix, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : Matrix.toEuclideanCLM (n := box.Edge) (𝕜 := ℂ) (1 : Matrix box.Edge box.Edge ℂ) = 1 := by
    ext x e
    change Matrix.mulVec (1 : Matrix box.Edge box.Edge ℂ) x e = x e
    rw [Matrix.one_mulVec]
  rw [he, map_sub, map_smul, h1]
  rfl

theorem complex_operator (m J : ℕ) (τ : ℚ) (hm : 0 < m) (hτ : 0 < τ)
    (j : Fin J) (hj : j.val ∉ bad P box m J τ) :
    (complexEquiv P box m J τ hm hτ j hj : EuclideanSpace ℂ box.Edge →L[ℂ] EuclideanSpace ℂ box.Edge) =
      Green.pecMaxwellOperator (material P box) - (rationalMidpoint τ J j.val : ℂ) • 1 := by
  rw [complexEquiv, ComplexInverse.complexEquiv_coe, shifted_complex_operator]

/-- Material validity is unconditional on the spectral event. -/
def shiftedMaterial (σ : ℚ) (hσ : 0 ≤ σ) (hroom : 64 * σ ≤ P.background.reserve) :
    ScalarMaterial box.nx box.ny box.nz where
  value c := (material P box).value c + 64 * σ
  bounds c := by
    have h := P.background.bounds (siteMod20 (Target.latticeCell c))
    change 1 ≤ P.background.material _ + 64 * σ ∧ P.background.material _ + 64 * σ ≤ 25
    constructor <;> linarith

theorem shifted_material_matrix (σ : ℚ) (hσ : 0 ≤ σ) (hroom : 64 * σ ≤ P.background.reserve) :
    (Target.maxwell (shiftedMaterial P box σ hσ hroom)).map Rat.cast = shiftedMatrix P box σ := by
  change (Target.operator box (fun c => (material P box).value c + 64 * σ)).map Rat.cast = _
  rw [Target.operator_uniform_shift]
  ext e f
  simp [shiftedMatrix, matrix, Target.maxwell, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

end Maxwell.Composition.PhysicalBackground
