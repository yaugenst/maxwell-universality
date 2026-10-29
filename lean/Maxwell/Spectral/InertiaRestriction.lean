import Maxwell.Spectral.InertiaCongruence
import Mathlib.LinearAlgebra.Projection

/-! Exact inertia splitting for an invariant subspace with a scalar
orthogonal complement. -/

noncomputable section

namespace Maxwell.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The complement contributes exactly its dimension when its scalar is
negative, and contributes no negative eigenvalues otherwise. -/
theorem negative_count_of_scalar_complement (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (K : Submodule ℂ H) (hK : ∀ x ∈ K, T x ∈ K) (a : ℝ)
    (hcomp : ∀ x : Kᗮ, T x = (a : ℂ) • (x : H)) :
    (Finset.univ.filter fun i => hT.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i =>
        (hT.restrict_invariant hK).eigenvalues rfl i < 0).card +
      if a < 0 then Module.finrank ℂ Kᗮ else 0 := by
  classical
  let A := T.restrict hK
  let S : Kᗮ →ₗ[ℂ] Kᗮ := (a : ℂ) • LinearMap.id
  let b := (hT.restrict_invariant hK).eigenvectorBasis rfl
  let d := stdOrthonormalBasis ℂ Kᗮ
  let μ := (hT.restrict_invariant hK).eigenvalues rfl
  have hqa : ∀ x : K, (inner ℂ x (A x)).re = ∑ i, μ i * ‖b.repr x i‖ ^ 2 :=
    spectral_quadratic_form (hT.restrict_invariant hK)
  have hqs : ∀ x : Kᗮ, (inner ℂ x (S x)).re = ∑ i, a * ‖d.repr x i‖ ^ 2 := by
    apply diagonal_quadratic_form d (fun _ => a)
    intro x i
    change d.repr ((a : ℂ) • x) i = (a : ℂ) * d.repr x i
    rw [map_smul]
    rfl
  let e : WithLp 2 (K × Kᗮ) ≃ₗ[ℂ] H :=
    (WithLp.linearEquiv 2 ℂ _).trans (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal)
  have hform (x : WithLp 2 (K × Kᗮ)) :
      (inner ℂ (e x) (T (e x))).re =
        (inner ℂ x (l2ProductMap A S x)).re := by
    change (inner ℂ ((x.ofLp.1 : H) + (x.ofLp.2 : H))
      (T ((x.ofLp.1 : H) + (x.ofLp.2 : H)))).re =
      (inner ℂ (x.ofLp.1 : H) (T (x.ofLp.1 : H)) +
        inner ℂ (x.ofLp.2 : H) ((a : ℂ) • (x.ofLp.2 : H))).re
    have hxy : inner ℂ (x.ofLp.1 : H) (x.ofLp.2 : H) = 0 :=
      (K.mem_orthogonal _).mp x.ofLp.2.property _ x.ofLp.1.property
    have hyAx : inner ℂ (x.ofLp.2 : H) (T (x.ofLp.1 : H)) = 0 :=
      (K.mem_orthogonal' _).mp x.ofLp.2.property _ (hK _ x.ofLp.1.property)
    simp only [map_add, hcomp x.ofLp.2, inner_add_left, inner_add_right,
      inner_smul_right, hxy, hyAx, add_zero, zero_add]
  have hc := card_negative_eq_of_diagonal_congruence
    (l2ProductMap A S) T (b.prod d) (hT.eigenvectorBasis rfl)
    (Sum.elim μ (fun _ => a)) (hT.eigenvalues rfl)
    (l2ProductMap_diagonal_quadratic_form A S b d μ (fun _ => a) hqa hqs)
    (spectral_quadratic_form hT) e hform
  rw [card_filter_sum_weights μ (fun _ : Fin (Module.finrank ℂ Kᗮ) => a) (fun z => z < 0)] at hc
  by_cases ha : a < 0
  · simpa only [ha, ite_true, Finset.filter_true, Finset.card_univ, Fintype.card_fin,
      μ] using hc.symm
  · simpa only [ha, ite_false, Finset.filter_false, Finset.card_empty, add_zero, μ] using hc.symm

/-- The scalar complement contributes zero multiplicity precisely when its scalar vanishes. -/
theorem zero_count_of_scalar_complement (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (K : Submodule ℂ H) (hK : ∀ x ∈ K, T x ∈ K) (a : ℝ)
    (hcomp : ∀ x : Kᗮ, T x = (a : ℂ) • (x : H)) :
    (Finset.univ.filter fun i => hT.eigenvalues rfl i = 0).card =
      (Finset.univ.filter fun i =>
        (hT.restrict_invariant hK).eigenvalues rfl i = 0).card +
      if a = 0 then Module.finrank ℂ Kᗮ else 0 := by
  classical
  let A := T.restrict hK
  let S : Kᗮ →ₗ[ℂ] Kᗮ := (a : ℂ) • LinearMap.id
  let b := (hT.restrict_invariant hK).eigenvectorBasis rfl
  let d := stdOrthonormalBasis ℂ Kᗮ
  let μ := (hT.restrict_invariant hK).eigenvalues rfl
  have hqa : ∀ x : K, (inner ℂ x (A x)).re = ∑ i, μ i * ‖b.repr x i‖ ^ 2 :=
    spectral_quadratic_form (hT.restrict_invariant hK)
  have hqs : ∀ x : Kᗮ, (inner ℂ x (S x)).re = ∑ i, a * ‖d.repr x i‖ ^ 2 := by
    apply diagonal_quadratic_form d (fun _ => a)
    intro x i
    change d.repr ((a : ℂ) • x) i = (a : ℂ) * d.repr x i
    rw [map_smul]
    rfl
  let e : WithLp 2 (K × Kᗮ) ≃ₗ[ℂ] H :=
    (WithLp.linearEquiv 2 ℂ _).trans (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal)
  have hform (x : WithLp 2 (K × Kᗮ)) :
      (inner ℂ (e x) (T (e x))).re =
        (inner ℂ x (l2ProductMap A S x)).re := by
    change (inner ℂ ((x.ofLp.1 : H) + (x.ofLp.2 : H))
      (T ((x.ofLp.1 : H) + (x.ofLp.2 : H)))).re =
      (inner ℂ (x.ofLp.1 : H) (T (x.ofLp.1 : H)) +
        inner ℂ (x.ofLp.2 : H) ((a : ℂ) • (x.ofLp.2 : H))).re
    have hxy : inner ℂ (x.ofLp.1 : H) (x.ofLp.2 : H) = 0 :=
      (K.mem_orthogonal _).mp x.ofLp.2.property _ x.ofLp.1.property
    have hyAx : inner ℂ (x.ofLp.2 : H) (T (x.ofLp.1 : H)) = 0 :=
      (K.mem_orthogonal' _).mp x.ofLp.2.property _ (hK _ x.ofLp.1.property)
    simp only [map_add, hcomp x.ofLp.2, inner_add_left, inner_add_right,
      inner_smul_right, hxy, hyAx, add_zero, zero_add]
  have hc := card_zero_eq_of_diagonal_congruence
    (l2ProductMap A S) T (b.prod d) (hT.eigenvectorBasis rfl)
    (Sum.elim μ (fun _ => a)) (hT.eigenvalues rfl)
    (l2ProductMap_diagonal_quadratic_form A S b d μ (fun _ => a) hqa hqs)
    (spectral_quadratic_form hT) e hform
  rw [card_filter_sum_weights μ (fun _ : Fin (Module.finrank ℂ Kᗮ) => a) (fun z => z = 0)] at hc
  by_cases ha : a = 0
  · simpa only [ha, ite_true, Finset.filter_true, Finset.card_univ, Fintype.card_fin,
      μ] using hc.symm
  · simpa only [ha, ite_false, Finset.filter_false, Finset.card_empty, add_zero, μ] using hc.symm

/-- A scalar shift turns a strict eigenvalue threshold into negative
inertia. This uses the original eigenbasis as an unsorted diagonalization,
so it does not assume a chosen shifted spectral ordering. -/
theorem threshold_count_eq_negative_of_shift
    (T B : H →ₗ[ℂ] H) (hT : T.IsSymmetric) (hB : B.IsSymmetric) (s : ℝ)
    (hshift : B = T - (s : ℂ) • LinearMap.id) :
    (Finset.univ.filter fun i => hT.eigenvalues rfl i < s).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  let b := hT.eigenvectorBasis rfl
  let μ := hT.eigenvalues rfl
  have hdiag (x : H) (i : Fin (Module.finrank ℂ H)) :
      b.repr (B x) i = ((μ i - s : ℝ) : ℂ) * b.repr x i := by
    rw [hshift]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    rw [hT.eigenvectorBasis_apply_self_apply rfl]
    change (μ i : ℂ) * b.repr x i - (s : ℂ) * b.repr x i = _
    ring
  have hquad := diagonal_quadratic_form b (fun i => μ i - s) hdiag
  have hc := card_negative_eq_of_diagonal_congruence B B b (hB.eigenvectorBasis rfl)
    (fun i => μ i - s) (hB.eigenvalues rfl) hquad (spectral_quadratic_form hB)
    (LinearEquiv.refl ℂ H) (fun _ => rfl)
  simpa only [sub_neg, μ] using hc

end Maxwell.Spectral
