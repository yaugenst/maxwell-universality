import Maxwell.Defect.RankOneGap

/-! Explicit finite small-parameter selection and the projected overlap
used to retain a nonzero defect numerator after rank-one branch selection. -/
namespace Maxwell.Defect
noncomputable section
open scoped Classical

/-- A finite family of linear strict inequalities with positive targets
holds on one explicitly chosen positive interval. -/
theorem exists_small_positive_linear {ι : Type*} [Fintype ι] [Nonempty ι]
    (coefficient target : ι → ℝ) (htarget : ∀ i, 0 < target i) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ : ℝ, 0 < τ → τ < η →
      ∀ i, coefficient i * τ < target i := by
  let bound := fun i => target i / (|coefficient i| + 1)
  let η := Finset.univ.inf' Finset.univ_nonempty bound
  have hη : 0 < η := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    exact div_pos (htarget i) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro τ hτ hτη i
  have hb : η ≤ bound i := Finset.inf'_le (f := bound) (Finset.mem_univ i)
  have hmul : τ * (|coefficient i| + 1) < target i :=
    (lt_div_iff₀ (by positivity)).mp (hτη.trans_le hb)
  have hcoeff : coefficient i ≤ |coefficient i| := le_abs_self _
  nlinarith

/-- Simultaneous scalar budgets for a nonzero selected spectral component.
The interval depends only on fixed reference data, not on the varying τ. -/
theorem exists_rankOne_small_scale (a b W c G K X : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hG : 0 < G) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ : ℝ, 0 < τ → τ < η →
      τ ≤ 1 ∧ τ * X ≤ 1 ∧ c * τ * (2*a^2 + b^2) ≤ G ∧
      4*K*τ ≤ c*a^2 ∧ W * (4*K/(c*a^2) + 2*X) * τ < a/2 := by
  let coefficient : Fin 5 → ℝ := ![1, X, c*(2*a^2+b^2), 4*K, W*(4*K/(c*a^2)+2*X)]
  let target : Fin 5 → ℝ := ![1, 1, G, c*a^2, a/2]
  have ht : ∀ i, 0 < target i := by
    intro i
    fin_cases i <;> dsimp [target] <;> positivity
  obtain ⟨η, hη, hsmall⟩ := exists_small_positive_linear coefficient target ht
  refine ⟨η, hη, ?_⟩
  intro τ hτ hτη
  have h0 := hsmall τ hτ hτη 0
  have h1 := hsmall τ hτ hτη 1
  have h2 := hsmall τ hτ hτη 2
  have h3 := hsmall τ hτ hτη 3
  have h4 := hsmall τ hτ hτη 4
  simp only [coefficient, target, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, one_mul] at h0 h1 h2 h3 h4
  exact ⟨h0.le, by nlinarith, by nlinarith, h3.le, h4⟩

/-- The original vector has strictly positive overlap with the normalized
projection onto the selected eigenspace. -/
theorem projected_normalized_overlap {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (lam : ℝ) (w : EuclideanSpace ℝ ι)
    (ha : spectralP d lam w ≠ 0) :
    inner ℝ w (‖spectralP d lam w‖⁻¹ • spectralP d lam w) = ‖spectralP d lam w‖ := by
  have hw : inner ℝ w (spectralP d lam w) = ‖spectralP d lam w‖^2 := by
    rw [real_inner_comm, spectralP_inner]
    simp
  rw [inner_smul_right, hw]
  have hn := norm_ne_zero_iff.mpr ha
  field_simp

/-- A quantitative eigenvector approximation preserves the nonzero
numerator, with an explicit half-overlap margin. -/
theorem projected_overlap_stable {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (lam : ℝ) (w u : EuclideanSpace ℝ ι)
    (ha : spectralP d lam w ≠ 0)
    (hclose : ‖w‖ * ‖u - ‖spectralP d lam w‖⁻¹ • spectralP d lam w‖ <
      ‖spectralP d lam w‖ / 2) :
    ‖spectralP d lam w‖ / 2 < inner ℝ w u := by
  have h := abs_real_inner_le_norm w (u - ‖spectralP d lam w‖⁻¹ • spectralP d lam w)
  rw [inner_sub_right, projected_normalized_overlap d lam w ha] at h
  have hlo := (abs_le.mp h).1
  linarith

end
end Maxwell.Defect
