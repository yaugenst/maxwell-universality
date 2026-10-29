import Maxwell.Continuum.FreeFiber
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Self-adjointness on the actual maximal free-fiber domain

Finite alias tests determine every coordinate of the adjoint. Consequently
the adjoint domain equals the maximal multiplier domain, rather than an
assumed common domain for different momenta.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

open scoped InnerProductSpace

section HilbertSum

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [DecidableEq ι]

theorem block_single_apply (B : ι → E →L[ℂ] E) (i : ι) (x : E) :
    (fun j => B j ((lp.single 2 i x : HilbertSum ι E) j)) =
      (lp.single 2 i (B i x) : HilbertSum ι E) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne _ _ _ h, map_zero]

theorem single_mem_maximalDomain (B : ι → E →L[ℂ] E) (i : ι) (x : E) :
    (lp.single 2 i x : HilbertSum ι E) ∈ maximalDomain B := by
  classical
  change Memℓp (fun j => B j ((lp.single 2 i x : HilbertSum ι E) j)) 2
  rw [block_single_apply]
  exact lp.memℓp _

theorem maximalOperator_single (B : ι → E →L[ℂ] E) (i : ι) (x : E) :
    maximalOperator B ⟨lp.single 2 i x, single_mem_maximalDomain B i x⟩ =
      lp.single 2 i (B i x) := by
  apply Subtype.ext
  exact block_single_apply B i x

/-- Finite-support sequences prove density of every maximal block domain. -/
theorem maximalDomain_dense (B : ι → E →L[ℂ] E) :
    Dense (maximalDomain B : Set (HilbertSum ι E)) := by
  classical
  intro u
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u)
  apply Filter.Eventually.of_forall
  intro s
  exact (maximalDomain B).sum_mem (fun i _ => single_mem_maximalDomain B i (u i))

omit [DecidableEq ι] in
theorem maximalOperator_symmetric (B : ι → E →L[ℂ] E)
    (hB : ∀ i, (B i).IsSymmetric) :
    (maximalOperator B).IsFormalAdjoint (maximalOperator B) := by
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact hB i (u.val i) (v.val i)

variable [CompleteSpace E]

/-- Testing the adjoint on one alias gives its literal block value. -/
theorem maximalOperator_adjoint_apply (B : ι → E →L[ℂ] E)
    (hB : ∀ i, (B i).IsSymmetric) (u : (maximalOperator B).adjoint.domain) (i : ι) :
    (maximalOperator B).adjoint u i = B i (u.val i) := by
  classical
  apply ext_inner_right ℂ
  intro x
  have h := LinearPMap.adjoint_isFormalAdjoint (maximalDomain_dense B) u
    ⟨lp.single 2 i x, single_mem_maximalDomain B i x⟩
  rw [maximalOperator_single, lp.inner_single_right, lp.inner_single_right] at h
  exact h.trans (hB i (u.val i) x).symm

/-- Self-adjoint blocks give a self-adjoint infinite multiplier on its full domain. -/
theorem maximalOperator_selfAdjoint (B : ι → E →L[ℂ] E)
    (hB : ∀ i, (B i).IsSymmetric) : IsSelfAdjoint (maximalOperator B) := by
  have hmem (u : (maximalOperator B).adjoint.domain) : u.val ∈ maximalDomain B := by
    change Memℓp (fun i => B i (u.val i)) 2
    have h := funext (maximalOperator_adjoint_apply B hB u)
    rw [← h]
    exact lp.memℓp _
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun u hu => hmem ⟨u, hu⟩, ?_⟩
    intro u v huv
    apply Subtype.ext
    funext i
    change (maximalOperator B).adjoint u i = B i (v.val i)
    rw [maximalOperator_adjoint_apply B hB, huv]
  · exact (maximalOperator_symmetric B hB).le_adjoint (maximalDomain_dense B)

end HilbertSum

def realMomentum (p : Fin 3 → ℝ) : Momentum := fun i => (p i : ℂ)

theorem real_blockMatrix_isHermitian (p : Fin 3 → ℝ) (E : ℝ) :
    (blockMatrix (realMomentum p) E).IsHermitian := by
  change (blockMatrix (realMomentum p) E).conjTranspose = blockMatrix (realMomentum p) E
  ext i j
  simp [Matrix.conjTranspose_apply, blockMatrix, momentumSquare, momentumOuter,
    realMomentum, Matrix.vecMulVec_apply, Matrix.one_apply, mul_comm, eq_comm]
  split_ifs <;> simp

theorem real_block_isSymmetric (p : Fin 3 → ℝ) (E : ℝ) :
    (block (realMomentum p) E).IsSymmetric := by
  change (blockMatrix (realMomentum p) E).toEuclideanLin.IsSymmetric
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (real_blockMatrix_isHermitian p E)

theorem aliasMomentum_real (q : Fin 3 → ℝ) (ν : Alias) :
    aliasMomentum (realMomentum q) ν =
      realMomentum (fun j => Real.pi / 2 + q j + Real.pi * (ν j : ℝ)) := by
  funext j
  simp [aliasMomentum, realMomentum]

/-- The real-momentum infinite free fiber is self-adjoint on its maximal domain. -/
theorem real_operator_selfAdjoint (q : Fin 3 → ℝ) (E : ℝ) :
    IsSelfAdjoint (operator (realMomentum q) E) := by
  apply maximalOperator_selfAdjoint
  intro ν
  rw [aliasMomentum_real]
  exact real_block_isSymmetric _ E

theorem real_freeFiber_selfAdjoint (q : Fin 3 → ℝ) :
    IsSelfAdjoint (freeFiber (realMomentum q)) := by
  exact real_operator_selfAdjoint q 7

end Maxwell.Continuum.FreeFiber
