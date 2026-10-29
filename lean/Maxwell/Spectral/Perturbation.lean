import Maxwell.Spectral.MinMax
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional spectral perturbation and inertia transfer

The comparisons use quadratic forms and the spectral theorem, with multiplicity.
An operator-norm displacement then bounds each ordered eigenvalue and transfers
open-interval eigenvalue counts to an enlarged center interval.
-/

namespace Maxwell.Spectral

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The span of eigenvectors above a threshold has exactly the expected
multiplicity and is bounded below by that threshold. -/
theorem exists_spectral_lower_subspace {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (c : ℝ) : ∃ W : Submodule ℂ H,
      Module.finrank ℂ W =
        (Finset.univ.filter fun i => c ≤ hA.eigenvalues rfl i).card ∧
      ∀ x : W, c * ‖(x : H)‖ ^ 2 ≤ Complex.re (inner ℂ (x : H) (A x)) := by
  classical
  let b := hA.eigenvectorBasis rfl
  let μ := hA.eigenvalues rfl
  let high := {i : Fin (Module.finrank ℂ H) // c ≤ μ i}
  let W := Submodule.span ℂ (Set.range fun i : high => b i)
  refine ⟨W, ?_, ?_⟩
  · have hli : LinearIndependent ℂ (fun i : high => b i) :=
      b.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective
    simpa only [W, high, μ, Fintype.card_subtype] using finrank_span_eq_card hli
  · intro x
    have hcoord (i : Fin (Module.finrank ℂ H)) (hi : ¬ c ≤ μ i) :
        b.repr (x : H) i = 0 := by
      have hx := x.property
      change (x : H) ∈ Submodule.span ℂ (Set.range fun i : high => b i) at hx
      refine Submodule.span_induction (p := fun y _ => b.repr y i = 0) ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨j, rfl⟩ := hy
        have hij : (j : Fin (Module.finrank ℂ H)) ≠ i := by
          intro he
          exact hi (he ▸ j.property)
        simp [b.repr_self, hij]
      · simp
      · intro y z _ _ hy hz
        simp [hy, hz]
      · intro a y _ hy
        simp [hy]
    rw [spectral_quadratic_form hA]
    have hn : ∑ i, ‖b.repr (x : H) i‖ ^ 2 = ‖(x : H)‖ ^ 2 := by
      simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right (x : H)
    rw [← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change c * ‖b.repr (x : H) i‖ ^ 2 ≤ μ i * ‖b.repr (x : H) i‖ ^ 2
    by_cases hi : c ≤ μ i
    · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    · simp only [hcoord i hi, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, le_refl]

/-- A quadratic-form comparison with a scalar error gives comparison of the
numbers of eigenvalues above translated thresholds. -/
theorem card_eigenvalues_ge_le_of_quadratic_le_add
    {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ε c : ℝ)
    (hAB : ∀ x : H, Complex.re (inner ℂ x (A x)) ≤
      Complex.re (inner ℂ x (B x)) + ε * ‖x‖ ^ 2) :
    (Finset.univ.filter fun i => c + ε ≤ hA.eigenvalues rfl i).card ≤
      (Finset.univ.filter fun i => c ≤ hB.eigenvalues rfl i).card := by
  obtain ⟨W, hdim, hW⟩ := exists_spectral_lower_subspace hA (c + ε)
  rw [← hdim]
  apply finrank_le_card_eigenvalues_ge hB W c
  intro x
  have hl := hW x
  have hu := hAB x
  nlinarith only [hl, hu]

/-- Ordered eigenvalues inherit a quadratic-form inequality, including its
scalar error. The ordering is the spectral theorem's decreasing ordering. -/
theorem eigenvalues_le_of_quadratic_le_add
    {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ε : ℝ)
    (hAB : ∀ x : H, Complex.re (inner ℂ x (A x)) ≤
      Complex.re (inner ℂ x (B x)) + ε * ‖x‖ ^ 2)
    (i : Fin (Module.finrank ℂ H)) :
    hA.eigenvalues rfl i ≤ hB.eigenvalues rfl i + ε := by
  classical
  by_contra hi
  have hlt : hB.eigenvalues rfl i < hA.eigenvalues rfl i - ε := by linarith
  have hc := card_eigenvalues_ge_le_of_quadratic_le_add hA hB ε
    (hA.eigenvalues rfl i - ε) hAB
  have hleft : i.val + 1 ≤
      (Finset.univ.filter fun j => hA.eigenvalues rfl i - ε + ε ≤
        hA.eigenvalues rfl j).card := by
    have hsub : Finset.Iic i ⊆
        Finset.univ.filter fun j => hA.eigenvalues rfl i - ε + ε ≤
          hA.eigenvalues rfl j := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        by simpa using hA.eigenvalues_antitone rfl (Finset.mem_Iic.mp hj)⟩
    simpa only [Fin.card_Iic] using Finset.card_le_card hsub
  have hright : (Finset.univ.filter fun j => hA.eigenvalues rfl i - ε ≤
      hB.eigenvalues rfl j).card ≤ i.val := by
    have hsub : (Finset.univ.filter fun j => hA.eigenvalues rfl i - ε ≤
        hB.eigenvalues rfl j) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hmono := hB.eigenvalues_antitone rfl (le_of_not_gt hji)
      have hj' := (Finset.mem_filter.mp hj).2
      linarith
    simpa only [Fin.card_Iio] using Finset.card_le_card hsub
  omega

/-- Loewner order, expressed at the authoritative quadratic-form boundary,
preserves every ordered eigenvalue. -/
theorem eigenvalues_mono_of_quadratic_le
    {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : ∀ x : H, Complex.re (inner ℂ x (A x)) ≤
      Complex.re (inner ℂ x (B x))) (i : Fin (Module.finrank ℂ H)) :
    hA.eigenvalues rfl i ≤ hB.eigenvalues rfl i := by
  simpa using eigenvalues_le_of_quadratic_le_add hA hB 0 (by simpa using hAB) i

omit [FiniteDimensional ℂ H] in
/-- The norm of the operator difference controls the difference of its real
quadratic forms. No self-adjointness is needed for this estimate. -/
theorem quadratic_le_add_of_norm_sub_le (A B : H →L[ℂ] H)
    (ε : ℝ) (hAB : ‖A - B‖ ≤ ε) (x : H) :
    Complex.re (inner ℂ x (A x)) ≤
      Complex.re (inner ℂ x (B x)) + ε * ‖x‖ ^ 2 := by
  have hx := ((A - B).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hAB (norm_nonneg x))
  have hinner : Complex.re (inner ℂ x ((A - B) x)) ≤ ε * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ x ((A - B) x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖(A - B) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (ε * ‖x‖) := mul_le_mul_of_nonneg_left hx (norm_nonneg x)
      _ = _ := by ring
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hinner
  linarith

/-- Weyl's norm perturbation bound for every ordered eigenvalue, with
multiplicities retained. -/
theorem eigenvalues_abs_sub_le_of_norm_sub_le (A B : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (ε : ℝ) (hAB : ‖A - B‖ ≤ ε) (i : Fin (Module.finrank ℂ H)) :
    |hA.eigenvalues rfl i - hB.eigenvalues rfl i| ≤ ε := by
  have hab := eigenvalues_le_of_quadratic_le_add hA hB ε
    (quadratic_le_add_of_norm_sub_le A B ε hAB) i
  have hba := eigenvalues_le_of_quadratic_le_add hB hA ε
    (quadratic_le_add_of_norm_sub_le B A ε (by simpa only [norm_sub_rev] using hAB)) i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A displaced open-band count is bounded by the center count on the band
widened by the operator-norm error. This supplies the local inertia bound
from a finite center certificate. -/
theorem card_eigenvalues_mem_Ioo_le_of_norm_sub_le (A B : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (ε : ℝ) (hAB : ‖A - B‖ ≤ ε) (a b : ℝ) :
    (Finset.univ.filter fun i => a < hB.eigenvalues rfl i ∧
      hB.eigenvalues rfl i < b).card ≤
    (Finset.univ.filter fun i => a - ε < hA.eigenvalues rfl i ∧
      hA.eigenvalues rfl i < b + ε).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  have hp := (Finset.mem_filter.mp hi).2
  have he := abs_le.mp (eigenvalues_abs_sub_le_of_norm_sub_le A B hA hB ε hAB i)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by constructor <;> linarith [he.1, he.2]⟩

/-- With center separation from both endpoints larger than the perturbation,
membership in the open interval is unchanged for each ordered eigenvalue. -/
theorem eigenvalues_mem_Ioo_iff_of_norm_sub_le (A B : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (ε : ℝ) (hAB : ‖A - B‖ ≤ ε) (a b : ℝ)
    (i : Fin (Module.finrank ℂ H))
    (ha : ε < |hA.eigenvalues rfl i - a|)
    (hb : ε < |hA.eigenvalues rfl i - b|) :
    (a < hB.eigenvalues rfl i ∧ hB.eigenvalues rfl i < b) ↔
      (a < hA.eigenvalues rfl i ∧ hA.eigenvalues rfl i < b) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hAB
  have he := abs_le.mp (eigenvalues_abs_sub_le_of_norm_sub_le A B hA hB ε hAB i)
  rcases lt_abs.mp ha with ha | ha <;> rcases lt_abs.mp hb with hb | hb <;>
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2, he.1, he.2]

/-- An interval's inertia count is constant under a norm perturbation smaller
than the center's distances from both endpoints. -/
theorem card_eigenvalues_mem_Ioo_eq_of_norm_sub_le (A B : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (ε : ℝ) (hAB : ‖A - B‖ ≤ ε) (a b : ℝ)
    (hgap : ∀ i, ε < |hA.eigenvalues rfl i - a| ∧
      ε < |hA.eigenvalues rfl i - b|) :
    (Finset.univ.filter fun i => a < hB.eigenvalues rfl i ∧
      hB.eigenvalues rfl i < b).card =
    (Finset.univ.filter fun i => a < hA.eigenvalues rfl i ∧
      hA.eigenvalues rfl i < b).card := by
  classical
  congr 1
  apply Finset.filter_congr
  intro i _
  exact eigenvalues_mem_Ioo_iff_of_norm_sub_le A B hA hB ε hAB a b i
    (hgap i).1 (hgap i).2

end

end Maxwell.Spectral
