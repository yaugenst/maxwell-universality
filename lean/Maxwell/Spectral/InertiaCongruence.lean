import Maxwell.Spectral.Perturbation
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Sylvester inertia under invertible congruence

The main comparison accepts any orthonormal diagonal representations, including
unsorted block representations. No nonsingularity of either quadratic form is
assumed; only the change of coordinates is invertible.
-/

namespace Maxwell.Spectral

noncomputable section

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The direct sum of two operators on the Hilbert product. -/
def l2ProductMap (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K) :
    WithLp 2 (H × K) →ₗ[ℂ] WithLp 2 (H × K) :=
  (A.prodMap B).withLpMap 2

/-- The product basis concatenates the two real diagonal quadratic forms. -/
theorem l2ProductMap_diagonal_quadratic_form
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (z : WithLp 2 (H × K)) :
    Complex.re (inner ℂ z (l2ProductMap A B z)) =
      ∑ i, Sum.elim μA μB i * ‖(bA.prod bB).repr z i‖ ^ 2 := by
  change Complex.re (inner ℂ (WithLp.ofLp z).1 (A (WithLp.ofLp z).1) +
    inner ℂ (WithLp.ofLp z).2 (B (WithLp.ofLp z).2)) = _
  rw [Complex.add_re, hquadA, hquadB, Fintype.sum_sum_type]
  congr 1

/-- Any sign predicate, or other predicate on real diagonal weights, counts
additively across a product diagonal representation. -/
theorem card_filter_sum_weights (μA : ι → ℝ) (μB : κ → ℝ) (p : ℝ → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun i => p (Sum.elim μA μB i)).card =
      (Finset.univ.filter fun i => p (μA i)).card +
        (Finset.univ.filter fun i => p (μB i)).card := by
  classical
  rw [← Finset.card_disjSum]
  congr 1
  ext i
  cases i <;> simp

/-- A nonnegative diagonal spectral subspace has dimension equal to the
number of nonnegative diagonal weights, including their multiplicities. -/
theorem exists_diagonal_nonnegative_subspace (A : H →ₗ[ℂ] H)
    (b : OrthonormalBasis ι ℂ H) (μ : ι → ℝ)
    (hquad : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μ i * ‖b.repr x i‖ ^ 2) :
    ∃ W : Submodule ℂ H,
      Module.finrank ℂ W = (Finset.univ.filter fun i => 0 ≤ μ i).card ∧
      ∀ x : W, 0 ≤ Complex.re (inner ℂ (x : H) (A x)) := by
  classical
  let high := {i : ι // 0 ≤ μ i}
  let W := Submodule.span ℂ (Set.range fun i : high => b i)
  refine ⟨W, ?_, ?_⟩
  · have hli : LinearIndependent ℂ (fun i : high => b i) :=
      b.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective
    simpa only [W, high, Fintype.card_subtype] using finrank_span_eq_card hli
  · intro x
    have hcoord (i : ι) (hi : ¬ 0 ≤ μ i) : b.repr (x : H) i = 0 := by
      have hx := x.property
      change (x : H) ∈ Submodule.span ℂ (Set.range fun i : high => b i) at hx
      refine Submodule.span_induction (p := fun y _ => b.repr y i = 0) ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨j, rfl⟩ := hy
        have hij : (j : ι) ≠ i := by
          intro he
          exact hi (he ▸ j.property)
        simp [b.repr_self, hij]
      · simp
      · intro y z _ _ hy hz
        simp [hy, hz]
      · intro a y _ hy
        simp [hy]
    rw [hquad]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : 0 ≤ μ i
    · exact mul_nonneg hi (sq_nonneg _)
    · simp [hcoord i hi]

private theorem card_nonnegative_le_of_diagonal_congruence
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => 0 ≤ μA i).card ≤
      (Finset.univ.filter fun i => 0 ≤ μB i).card := by
  obtain ⟨W, hdim, hW⟩ := exists_diagonal_nonnegative_subspace A bA μA hquadA
  rw [← hdim, ← e.finrank_map_eq W]
  apply quadratic_minmax_count bB μB hquadB (W.map e.toLinearMap) 0
  intro y
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.property
  have hp := hW ⟨x, hx⟩
  simp only [zero_mul]
  rw [← hxy]
  change 0 ≤ Complex.re (inner ℂ (e x) (B (e x)))
  rw [hform]
  exact hp

/-- Sylvester's law for nonnegative weights in arbitrary orthonormal diagonal
representations. The diagonal lists need not be sorted. -/
theorem card_nonnegative_eq_of_diagonal_congruence
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => 0 ≤ μA i).card =
      (Finset.univ.filter fun i => 0 ≤ μB i).card := by
  apply le_antisymm
  · exact card_nonnegative_le_of_diagonal_congruence A B bA bB μA μB hquadA hquadB e hform
  · apply card_nonnegative_le_of_diagonal_congruence B A bB bA μB μA hquadB hquadA e.symm
    intro y
    simpa only [e.apply_symm_apply] using (hform (e.symm y)).symm

/-- Strict negative multiplicity is preserved by invertible congruence,
including when either form has a nontrivial kernel. -/
theorem card_negative_eq_of_diagonal_congruence
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => μA i < 0).card =
      (Finset.univ.filter fun i => μB i < 0).card := by
  classical
  have hc := card_nonnegative_eq_of_diagonal_congruence A B bA bB μA μB hquadA hquadB e hform
  have hn : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis bA.toBasis, ← Module.finrank_eq_card_basis bB.toBasis]
    exact e.finrank_eq
  have ha := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => 0 ≤ μA i)
  have hb := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => 0 ≤ μB i)
  simp only [not_le, Finset.card_univ] at ha hb
  omega

/-- Positive multiplicity follows by negating the two represented forms;
no ordering convention for the negated spectrum is required. -/
theorem card_positive_eq_of_diagonal_congruence
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => 0 < μA i).card =
      (Finset.univ.filter fun i => 0 < μB i).card := by
  have hA : ∀ x : H, Complex.re (inner ℂ x ((-A) x)) =
      ∑ i, (-μA i) * ‖bA.repr x i‖ ^ 2 := by
    intro x
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, hquadA,
      neg_mul, Finset.sum_neg_distrib]
  have hB : ∀ y : K, Complex.re (inner ℂ y ((-B) y)) =
      ∑ i, (-μB i) * ‖bB.repr y i‖ ^ 2 := by
    intro y
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, hquadB,
      neg_mul, Finset.sum_neg_distrib]
  have hf : ∀ x : H, Complex.re (inner ℂ (e x) ((-B) (e x))) =
      Complex.re (inner ℂ x ((-A) x)) := by
    intro x
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, hform]
  simpa only [neg_lt_zero] using
    card_negative_eq_of_diagonal_congruence (-A) (-B) bA bB
      (fun i => -μA i) (fun i => -μB i) hA hB e hf

private theorem card_nonnegative_eq_card_zero_add_positive (ν : ι → ℝ) :
    (Finset.univ.filter fun i => 0 ≤ ν i).card =
      (Finset.univ.filter fun i => ν i = 0).card +
        (Finset.univ.filter fun i => 0 < ν i).card := by
  classical
  rw [← Finset.card_union_of_disjoint (s := Finset.univ.filter fun i => ν i = 0)
    (t := Finset.univ.filter fun i => 0 < ν i) (by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have he := (Finset.mem_filter.mp hi).2
      have hg := (Finset.mem_filter.mp hj).2
      linarith)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  exact le_iff_eq_or_lt'

/-- The zero multiplicity is also preserved, without a nonsingularity
hypothesis on the forms. -/
theorem card_zero_eq_of_diagonal_congruence
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (bA : OrthonormalBasis ι ℂ H) (bB : OrthonormalBasis κ ℂ K)
    (μA : ι → ℝ) (μB : κ → ℝ)
    (hquadA : ∀ x : H, Complex.re (inner ℂ x (A x)) = ∑ i, μA i * ‖bA.repr x i‖ ^ 2)
    (hquadB : ∀ y : K, Complex.re (inner ℂ y (B y)) = ∑ i, μB i * ‖bB.repr y i‖ ^ 2)
    (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => μA i = 0).card =
      (Finset.univ.filter fun i => μB i = 0).card := by
  classical
  have hc := card_nonnegative_eq_of_diagonal_congruence A B bA bB μA μB hquadA hquadB e hform
  have hp := card_positive_eq_of_diagonal_congruence A B bA bB μA μB hquadA hquadB e hform
  have hsplitB := card_nonnegative_eq_card_zero_add_positive μB
  have hsplitA := card_nonnegative_eq_card_zero_add_positive μA
  omega

section Spectral

variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]

/-- Abstract positive Schur-block bookkeeping. The positive material block
contributes the entire electric dimension; the identity block contributes
the entire magnetic dimension. Actual matrix congruences can instantiate
this theorem without re-elaborating their inverse formulas in spectral bases. -/
theorem positive_schur_negative_count (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K)
    (M : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hM : M.IsSymmetric)
    (hMpos : ∀ i, 0 < hM.eigenvalues rfl i)
    (e : WithLp 2 (H × K) ≃ₗ[ℂ] WithLp 2 (H × K))
    (hform : ∀ x : WithLp 2 (H × K),
      Complex.re (inner ℂ (e x) (l2ProductMap M (-B) (e x))) =
        Complex.re (inner ℂ x (l2ProductMap (-A) LinearMap.id x))) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card + Module.finrank ℂ K =
      Module.finrank ℂ H + (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  classical
  have hqa : ∀ x : H, Complex.re (inner ℂ x ((-A) x)) =
      ∑ i, (-hA.eigenvalues rfl i) * ‖(hA.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
    intro x
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re,
      spectral_quadratic_form hA, neg_mul, Finset.sum_neg_distrib]
  have hqb : ∀ x : K, Complex.re (inner ℂ x ((-B) x)) =
      ∑ i, (-hB.eigenvalues rfl i) * ‖(hB.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
    intro x
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re,
      spectral_quadratic_form hB, neg_mul, Finset.sum_neg_distrib]
  have hqi : ∀ x : K, Complex.re (inner ℂ x (LinearMap.id x)) =
      ∑ i, (1 : ℝ) * ‖(hB.eigenvectorBasis rfl).repr x i‖ ^ 2 :=
    diagonal_quadratic_form (hB.eigenvectorBasis rfl) (fun _ => 1) (by intros; simp)
  have hc := card_positive_eq_of_diagonal_congruence
    (l2ProductMap (-A) LinearMap.id) (l2ProductMap M (-B))
    ((hA.eigenvectorBasis rfl).prod (hB.eigenvectorBasis rfl))
    ((hM.eigenvectorBasis rfl).prod (hB.eigenvectorBasis rfl))
    (Sum.elim (fun i => -hA.eigenvalues rfl i) (fun _ => 1))
    (Sum.elim (hM.eigenvalues rfl) (fun i => -hB.eigenvalues rfl i))
    (l2ProductMap_diagonal_quadratic_form (-A) LinearMap.id
      (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
      (fun i => -hA.eigenvalues rfl i) (fun _ => 1) hqa hqi)
    (l2ProductMap_diagonal_quadratic_form M (-B)
      (hM.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
      (hM.eigenvalues rfl) (fun i => -hB.eigenvalues rfl i) (spectral_quadratic_form hM) hqb)
    e hform
  rw [card_filter_sum_weights, card_filter_sum_weights] at hc
  simpa only [neg_pos, zero_lt_one, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin, hMpos] using hc

/-- Multiplication by a strictly positive real scalar preserves negative
eigenvalue multiplicity. The scalar acts through the real normed structure. -/
theorem positive_scalar_negative_count (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (t : ℝ) (ht : 0 < t) (hTA : (t • A).IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hTA.eigenvalues rfl i < 0).card := by
  have hquad : ∀ x : H, Complex.re (inner ℂ x ((t • A) x)) =
      ∑ i, (t * hA.eigenvalues rfl i) * ‖(hA.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
    intro x
    simp only [LinearMap.smul_apply, inner_smul_right_eq_smul, Complex.smul_re,
      smul_eq_mul, spectral_quadratic_form hA, Finset.mul_sum, mul_assoc]
  have hc := card_negative_eq_of_diagonal_congruence (t • A) (t • A)
    (hA.eigenvectorBasis rfl) (hTA.eigenvectorBasis rfl)
    (fun i => t * hA.eigenvalues rfl i) (hTA.eigenvalues rfl)
    hquad (spectral_quadratic_form hTA) (LinearEquiv.refl ℂ H) (fun _ => rfl)
  simpa only [mul_neg_iff, ht, not_lt_of_ge ht.le, false_and, or_false, false_or,
    true_and] using hc

/-- Sylvester inertia for the actual finite selfadjoint eigenvalue lists,
including negative, zero, and positive multiplicities. -/
theorem eigenvalue_inertia_congruence {A : H →ₗ[ℂ] H} {B : K →ₗ[ℂ] K}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (e : H ≃ₗ[ℂ] K)
    (hform : ∀ x : H, Complex.re (inner ℂ (e x) (B (e x))) =
      Complex.re (inner ℂ x (A x))) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card ∧
    (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i = 0).card ∧
    (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card =
      (Finset.univ.filter fun i => 0 < hB.eigenvalues rfl i).card := by
  exact ⟨card_negative_eq_of_diagonal_congruence A B
      (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
      (hA.eigenvalues rfl) (hB.eigenvalues rfl)
      (spectral_quadratic_form hA) (spectral_quadratic_form hB) e hform,
    card_zero_eq_of_diagonal_congruence A B
      (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
      (hA.eigenvalues rfl) (hB.eigenvalues rfl)
      (spectral_quadratic_form hA) (spectral_quadratic_form hB) e hform,
    card_positive_eq_of_diagonal_congruence A B
      (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
      (hA.eigenvalues rfl) (hB.eigenvalues rfl)
      (spectral_quadratic_form hA) (spectral_quadratic_form hB) e hform⟩

end Spectral
end
end Maxwell.Spectral
