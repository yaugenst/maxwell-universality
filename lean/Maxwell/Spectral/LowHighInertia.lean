import Maxwell.Spectral.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact inertia from finite trial spaces and a coercive high complement.
The coupling estimate is expressed in the actual Hilbert quadratic form. -/

noncomputable section

namespace Maxwell.Spectral

open Finset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- A strictly positive form on an injected trial family forces at least its
dimension of positive eigenvalues. Injectivity follows from the strict form. -/
theorem finrank_le_card_positive_of_trial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (F : V →ₗ[ℂ] H)
    (hF : ∀ x : V, x ≠ 0 → 0 < (inner ℂ (F x) (A (F x))).re) :
    Module.finrank ℂ V ≤
      (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card := by
  classical
  let positive := {i : Fin (Module.finrank ℂ H) // 0 < hA.eigenvalues rfl i}
  let b := hA.eigenvectorBasis rfl
  let f : V →ₗ[ℂ] (positive → ℂ) :=
    { toFun := fun x i => b.repr (F x) i
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hne
    have hpos := hF x hne
    rw [spectral_quadratic_form hA] at hpos
    have hterm (i : Fin (Module.finrank ℂ H)) :
        hA.eigenvalues rfl i * ‖b.repr (F x) i‖ ^ 2 ≤ 0 := by
      by_cases hi : 0 < hA.eigenvalues rfl i
      · have hz : b.repr (F x) i = 0 := congrFun hx (⟨i, hi⟩ : positive)
        simp [hz]
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) (sq_nonneg _)
    exact (not_lt_of_ge (Finset.sum_nonpos fun i _ => hterm i)) hpos
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa [positive, Fintype.card_subtype] using hd

/-- The negative version uses the same eigenbasis with the signs reversed. -/
theorem finrank_le_card_negative_of_trial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (F : V →ₗ[ℂ] H)
    (hF : ∀ x : V, x ≠ 0 → (inner ℂ (F x) (A (F x))).re < 0) :
    Module.finrank ℂ V ≤
      (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card := by
  classical
  let negative := {i : Fin (Module.finrank ℂ H) // hA.eigenvalues rfl i < 0}
  let b := hA.eigenvectorBasis rfl
  let f : V →ₗ[ℂ] (negative → ℂ) :=
    { toFun := fun x i => b.repr (F x) i
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hne
    have hneg := hF x hne
    rw [spectral_quadratic_form hA] at hneg
    have hterm (i : Fin (Module.finrank ℂ H)) :
        0 ≤ hA.eigenvalues rfl i * ‖b.repr (F x) i‖ ^ 2 := by
      by_cases hi : hA.eigenvalues rfl i < 0
      · have hz : b.repr (F x) i = 0 := congrFun hx (⟨i, hi⟩ : negative)
        simp [hz]
      · exact mul_nonneg (le_of_not_gt hi) (sq_nonneg _)
    exact (not_lt_of_ge (Finset.sum_nonneg fun i _ => hterm i)) hneg
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa [negative, Fintype.card_subtype] using hd

/-- Strictly negative and positive trial families whose dimensions exhaust
the ambient space determine the complete inertia, including nonsingularity. -/
theorem inertia_of_complementary_trials
    {N P : Type*} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (Fneg : N →ₗ[ℂ] H) (Fpos : P →ₗ[ℂ] H)
    (hneg : ∀ x : N, x ≠ 0 → (inner ℂ (Fneg x) (A (Fneg x))).re < 0)
    (hpos : ∀ x : P, x ≠ 0 → 0 < (inner ℂ (Fpos x) (A (Fpos x))).re)
    (hdim : Module.finrank ℂ N + Module.finrank ℂ P = Module.finrank ℂ H) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card = Module.finrank ℂ N ∧
    (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card = 0 ∧
    (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card = Module.finrank ℂ P := by
  classical
  have hn := finrank_le_card_negative_of_trial A hA Fneg hneg
  have hp := finrank_le_card_positive_of_trial A hA Fpos hpos
  have hsplit :
      (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card +
        (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card +
        (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card =
      Module.finrank ℂ H := by
    have h₁ := Finset.card_filter_add_card_filter_not (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℂ H))))
      (p := fun i => hA.eigenvalues rfl i < 0)
    have h₂ := Finset.card_filter_add_card_filter_not (s :=
      Finset.univ.filter fun i => ¬ hA.eigenvalues rfl i < 0)
      (p := fun i => hA.eigenvalues rfl i = 0)
    have heq : (Finset.univ.filter fun i => ¬ hA.eigenvalues rfl i < 0).filter
        (fun i => hA.eigenvalues rfl i = 0) =
        Finset.univ.filter fun i => hA.eigenvalues rfl i = 0 := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor
      · exact And.right
      · intro h; exact ⟨by rw [h]; exact lt_irrefl 0, h⟩
    have hgt : (Finset.univ.filter fun i => ¬ hA.eigenvalues rfl i < 0).filter
        (fun i => ¬ hA.eigenvalues rfl i = 0) =
        Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2),
        fun h => ⟨h.le, ne_of_gt h⟩⟩
    rw [heq, hgt] at h₂
    simp only [Finset.card_univ, Fintype.card_fin] at h₁
    omega
  omega

/-- The scalar Schur estimate controlling the low-positive/high coupling. -/
theorem positive_low_high_quadratic {a μ r x y : ℝ}
    (ha : 0 < a) (_hμ : 0 < μ) (_hr : 0 ≤ r) (hgap : r ^ 2 < a * μ)
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x ^ 2 - 2 * r * x * y + μ * y ^ 2 := by
  by_cases hy0 : y = 0
  · rcases hne with hxn | hyn
    · subst y
      simpa using mul_pos ha (sq_pos_of_ne_zero hxn)
    · exact (hyn hy0).elim
  · have hs := sq_nonneg (a * x - r * y)
    have hp := mul_pos (sub_pos.mpr hgap) (sq_pos_of_ne_zero hy0)
    nlinarith

omit [FiniteDimensional ℂ H] in
/-- A positive low block remains positive after coupling it to a coercive
high block when the squared residual bound is below the product of margins. -/
theorem positive_low_high_trial
    {P K : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (F : P →ₗ[ℂ] H) (G : K →ₗ[ℂ] H) (a μ r : ℝ)
    (ha : 0 < a) (hμ : 0 < μ) (hr : 0 ≤ r) (hgap : r ^ 2 < a * μ)
    (hF : ∀ p, a * ‖p‖ ^ 2 ≤ (inner ℂ (F p) (A (F p))).re)
    (hG : ∀ k, μ * ‖k‖ ^ 2 ≤ (inner ℂ (G k) (A (G k))).re)
    (hc : ∀ p k, |(inner ℂ (F p) (A (G k))).re| ≤ r * ‖p‖ * ‖k‖)
    (x : P × K) (hx : x ≠ 0) :
    0 < (inner ℂ (F x.1 + G x.2) (A (F x.1 + G x.2))).re := by
  have hne : ‖x.1‖ ≠ 0 ∨ ‖x.2‖ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Prod.ext (norm_eq_zero.mp h.1) (norm_eq_zero.mp h.2))
  have hq := positive_low_high_quadratic ha hμ hr hgap (norm_nonneg x.1)
    (norm_nonneg x.2) hne
  have hc' := (abs_le.mp (hc x.1 x.2)).1
  have hsym : (inner ℂ (G x.2) (A (F x.1))).re =
      (inner ℂ (F x.1) (A (G x.2))).re := by
    rw [← hA (G x.2) (F x.1)]
    exact inner_re_symm (𝕜 := ℂ) (A (G x.2)) (F x.1)
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
  rw [hsym]
  linarith [hF x.1, hG x.2]

/-- The finite low negative family and the low-positive/high family certify
exact full inertia. No eigenvalue-count premise is used. -/
theorem inertia_of_low_high_trials
    {N P K : Type*} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [FiniteDimensional ℂ K]
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (Fneg : N →ₗ[ℂ] H) (Fpos : P →ₗ[ℂ] H) (G : K →ₗ[ℂ] H)
    (a μ r : ℝ) (ha : 0 < a) (hμ : 0 < μ) (hr : 0 ≤ r) (hgap : r ^ 2 < a * μ)
    (hneg : ∀ x : N, x ≠ 0 → (inner ℂ (Fneg x) (A (Fneg x))).re < 0)
    (hpos : ∀ p, a * ‖p‖ ^ 2 ≤ (inner ℂ (Fpos p) (A (Fpos p))).re)
    (hhigh : ∀ k, μ * ‖k‖ ^ 2 ≤ (inner ℂ (G k) (A (G k))).re)
    (hc : ∀ p k, |(inner ℂ (Fpos p) (A (G k))).re| ≤ r * ‖p‖ * ‖k‖)
    (hdim : Module.finrank ℂ N + (Module.finrank ℂ P + Module.finrank ℂ K) =
      Module.finrank ℂ H) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card = Module.finrank ℂ N ∧
    (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card = 0 ∧
    (Finset.univ.filter fun i => 0 < hA.eigenvalues rfl i).card =
      Module.finrank ℂ P + Module.finrank ℂ K := by
  let L : P × K →ₗ[ℂ] H := Fpos.coprod G
  have hL : ∀ x, x ≠ 0 → 0 < (inner ℂ (L x) (A (L x))).re :=
    positive_low_high_trial A hA Fpos G a μ r ha hμ hr hgap hpos hhigh hc
  simpa only [Module.finrank_prod] using
    inertia_of_complementary_trials A hA Fneg L hneg hL (by
      simpa only [Module.finrank_prod] using hdim)

end Maxwell.Spectral
