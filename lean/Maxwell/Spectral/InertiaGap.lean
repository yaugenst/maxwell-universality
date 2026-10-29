import Maxwell.Spectral.MinMax
import Mathlib.Tactic

namespace Maxwell.Spectral

noncomputable section

/-- Two original threshold counts plus the one-sided material perturbation
bound exclude every other perturbed eigenvalue between the transported
thresholds. The two retained eigenvalues are located independently. -/
theorem outside_pair_of_threshold_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : ι → ℝ) (a b ρ : ℝ) (hab : a ≤ b)
    (hcomparison : ∀ i, ν i ≤ μ i ∧ μ i ≤ ν i + ρ)
    (hcounts : (Finset.univ.filter fun i => μ i < b).card ≤
      (Finset.univ.filter fun i => μ i < a).card + 2)
    (i j : ι) (hij : i ≠ j)
    (hi : a < ν i ∧ ν i < b - ρ) (hj : a < ν j ∧ ν j < b - ρ)
    (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : ν k ≤ a ∨ b - ρ ≤ ν k := by
  classical
  let A := Finset.univ.filter fun i => μ i < a
  let B := Finset.univ.filter fun i => μ i < b
  let F := Finset.univ.filter fun i => a < ν i ∧ ν i < b - ρ
  have hAB : A ⊆ B := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ l,
      ((Finset.mem_filter.mp hl).2).trans_le hab⟩
  have hdiff : (B \ A).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset hAB]
    change B.card ≤ A.card + 2 at hcounts
    omega
  have hFsub : F ⊆ B \ A := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have hc := hcomparison l
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, by linarith [hc.2, hl'.2]⟩
    · intro hla
      have hla' := (Finset.mem_filter.mp hla).2
      linarith [hc.1, hl'.1]
  have hFcard : F.card ≤ 2 := (Finset.card_le_card hFsub).trans hdiff
  have hpair : ({i, j} : Finset ι) ⊆ F := by
    intro l hl
    rcases Finset.mem_insert.mp hl with hl | hl
    · subst l
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    · have hl' : l = j := Finset.mem_singleton.mp hl
      subst l
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have heq : ({i, j} : Finset ι) = F := Finset.eq_of_subset_of_card_le hpair
    (by simpa only [Finset.card_pair hij] using hFcard)
  by_cases hka : ν k ≤ a
  · exact Or.inl hka
  · right
    by_contra hkb
    have hk : k ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_univ k, lt_of_not_ge hka, lt_of_not_ge hkb⟩
    rw [← heq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    exact hk.elim hki hkj

end
end Maxwell.Spectral
