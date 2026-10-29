import Maxwell.Composition.SignedMediator

/-! Finite direct-sum algebra for subdivision paths. Endpoint couplings are
actual matrix entries; all path contributions remain in their own blocks. -/

noncomputable section

namespace Maxwell.Composition.SubdivisionBlocks

open Matrix
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {I : E → Type*} [∀ e, Fintype (I e)] [∀ e, DecidableEq (I e)]

def coupling (G : SignedIncidence V E) (first last : ∀ e, I e) : Matrix V (Σ e, I e) ℝ :=
  fun v t => (if t.2 = first t.1 ∧ v = G.tail t.1 then 1 else 0) +
    (if t.2 = last t.1 ∧ v = G.head t.1 then G.sign t.1 else 0)

omit [Fintype V] in
theorem coupling_mul_blockDiagonal (G : SignedIncidence V E) (first last : ∀ e, I e)
    (D : ∀ e, Matrix (I e) (I e) ℝ) (v : V) (e : E) (t : I e) :
    (coupling G first last * Matrix.blockDiagonal' D) v ⟨e, t⟩ =
      (if v = G.tail e then D e (first e) t else 0) +
      (if v = G.head e then G.sign e * D e (last e) t else 0) := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single e]
  · simp [coupling, ite_and, add_mul, Finset.sum_add_distrib, ite_mul]
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro s _
    rw [Matrix.blockDiagonal'_apply_ne D s t hfe, mul_zero]
  · simp

omit [Fintype V] in
theorem schur_correction (G : SignedIncidence V E) (first last : ∀ e, I e)
    (D : ∀ e, Matrix (I e) (I e) ℝ)
    (hff : ∀ e, D e (first e) (first e) = 0)
    (hll : ∀ e, D e (last e) (last e) = 0)
    (hfl : ∀ e, D e (first e) (last e) = -1)
    (hlf : ∀ e, D e (last e) (first e) = -1) :
    coupling G first last * Matrix.blockDiagonal' D * (coupling G first last).transpose =
      -G.adjacency := by
  ext v w
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  simp only [coupling_mul_blockDiagonal, Matrix.transpose_apply]
  change (∑ e, ∑ t, _ * coupling G first last w ⟨e, t⟩) = -∑ e, _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp [coupling, ite_and, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, hff, hll, hfl, hlf]
  split_ifs <;> ring

omit [Fintype V] [DecidableEq E] in
theorem coupling_row_abs_sum_le (G : SignedIncidence V E) (first last : ∀ e, I e) (v : V) :
    ∑ t, |coupling G first last v t| ≤ G.degree v := by
  rw [Fintype.sum_sigma]
  unfold SignedIncidence.degree
  apply Finset.sum_le_sum
  intro e _
  calc
    _ ≤ ∑ t : I e,
        (|(if t = first e ∧ v = G.tail e then (1 : ℝ) else 0)| +
          |(if t = last e ∧ v = G.head e then G.sign e else 0)|) :=
      Finset.sum_le_sum (fun t _ => abs_add_le _ _)
    _ = (if v = G.tail e then 1 else 0) + (if v = G.head e then 1 else 0) := by
      simp only [abs_ite, abs_one, abs_zero, G.abs_sign, ite_and,
        Finset.sum_add_distrib]
      simp
    _ = _ := by
      have hdistinct := G.distinct e
      by_cases ht : v = G.tail e <;> by_cases hh : v = G.head e <;> simp_all

omit [Fintype E] [DecidableEq E] [∀ e, Fintype (I e)] in
theorem coupling_col_abs_sum_le (G : SignedIncidence V E) (first last : ∀ e, I e)
    (hdistinct : ∀ e, first e ≠ last e) (t : Σ e, I e) :
    ∑ v, |coupling G first last v t| ≤ 1 := by
  rcases t with ⟨e, t⟩
  calc
    _ ≤ ∑ v : V,
        (|(if t = first e ∧ v = G.tail e then (1 : ℝ) else 0)| +
          |(if t = last e ∧ v = G.head e then G.sign e else 0)|) :=
      Finset.sum_le_sum (fun v _ => abs_add_le _ _)
    _ = (if t = first e then 1 else 0) + (if t = last e then 1 else 0) := by
      simp only [abs_ite, abs_one, abs_zero, G.abs_sign, ite_and,
        Finset.sum_add_distrib]
      simp
    _ ≤ _ := by
      by_cases hf : t = first e
      · have hl : t ≠ last e := fun h => hdistinct e (hf.symm.trans h)
        rw [ite_eq_left hf, ite_eq_right hl]
        norm_num
      · by_cases hl : t = last e
        · rw [ite_eq_right hf, ite_eq_left hl]
          norm_num
        · rw [ite_eq_right hf, ite_eq_right hl]
          norm_num

theorem coupling_norm_le_two (G : SignedIncidence V E) (first last : ∀ e, I e)
    (hdistinct : ∀ e, first e ≠ last e) (hdegree : ∀ v, G.degree v ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (coupling G first last)‖ ≤ 2 := by
  have h := Maxwell.rectangularEuclideanCLM_norm_le_sqrt (coupling G first last) 3 1
    (by norm_num) (by norm_num)
    (fun v => (coupling_row_abs_sum_le G first last v).trans (hdegree v))
    (coupling_col_abs_sum_le G first last hdistinct)
  refine h.trans ?_
  norm_num only [mul_one]
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

theorem blockDiagonal_norm_le (D : ∀ e, Matrix (I e) (I e) ℝ)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hr : ∀ e i, ∑ j, |D e i j| ≤ ell)
    (hc : ∀ e j, ∑ i, |D e i j| ≤ ell) :
    ‖Matrix.toEuclideanCLM (n := Σ e, I e) (𝕜 := ℝ) (Matrix.blockDiagonal' D)‖ ≤ ell := by
  apply Maxwell.matrix_toEuclideanCLM_norm_le _ ell hell
  · rintro ⟨e, i⟩
    rw [Fintype.sum_sigma, Finset.sum_eq_single e]
    · simpa using hr e i
    · intro f _ hfe
      apply Finset.sum_eq_zero
      intro j _
      rw [Matrix.blockDiagonal'_apply_ne D i j (Ne.symm hfe), abs_zero]
    · simp
  · rintro ⟨e, j⟩
    rw [Fintype.sum_sigma, Finset.sum_eq_single e]
    · simpa using hc e j
    · intro f _ hfe
      apply Finset.sum_eq_zero
      intro i _
      rw [Matrix.blockDiagonal'_apply_ne D i j hfe, abs_zero]
    · simp

end Maxwell.Composition.SubdivisionBlocks
