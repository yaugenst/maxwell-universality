import Maxwell.Continuum.PeriodicSamplingProduct

/-! Certified coefficient errors for an actual finite product grid,
controlled by the full Fourier tail outside an integer cube. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open scoped Classical

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (N : ℕ) [NeZero N]

def cubeTail (c : (ι → ℤ) → E) (R : ℤ) : ℝ :=
  ∑' n, if ∃ i, R ≤ |n i| then ‖c n‖ else 0

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem cubeTail_summable (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖)) (R : ℤ) :
    Summable (fun n => if ∃ i, R ≤ |n i| then ‖c n‖ else 0) := by
  apply Summable.of_nonneg_of_le _ _ hc
  · intro n
    split_ifs <;> positivity
  · intro n
    split_ifs <;> simp

omit [NeZero N] in
theorem alias_outside_cube {n k : ι → ℤ} {K : ℕ} (hk : ∀ i, |k i| ≤ K)
    (hne : n ≠ k) (hmod : frequency N n = frequency N k) :
    ∃ i, (N : ℤ)-K ≤ |n i| := by
  have hi : ∃ i, n i ≠ k i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i,hi⟩ := hi
  have hm : (n i : ZMod N) = (k i : ZMod N) := congrFun hmod i
  have hr := PeriodicSampling.alias_radius N hi hm
  exact ⟨i,by have := hk i; omega⟩

def aliasRemainder (c : (ι → ℤ) → E) (k n : ι → ℤ) : E :=
  if n = k then 0 else if frequency N n = frequency N k then c n else 0

omit [NormedSpace ℂ E] [CompleteSpace E] [NeZero N] in
theorem aliasRemainder_norm_le (c : (ι → ℤ) → E) (k n : ι → ℤ) :
    ‖aliasRemainder N c k n‖ ≤ ‖c n‖ := by
  unfold aliasRemainder
  split_ifs <;> simp

omit [NormedSpace ℂ E] [CompleteSpace E] [NeZero N] in
theorem aliasRemainder_summable_norm (c : (ι → ℤ) → E)
    (hc : Summable (fun n => ‖c n‖)) (k : ι → ℤ) :
    Summable (fun n => ‖aliasRemainder N c k n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (aliasRemainder_norm_le N c k) hc

theorem coefficient_samples_sub (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖))
    (k : ι → ℤ) :
    coefficient N (fun j => synthesis c (fun i => ((j i).val : ℝ)/N)) (frequency N k)-c k =
      ∑' n, aliasRemainder N c k n := by
  rw [coefficient_samples N c hc k]
  have hs : Summable (fun n => if frequency N n = frequency N k then c n else 0) := by
    apply Summable.of_norm_bounded hc
    intro n
    split_ifs <;> simp
  rw [hs.tsum_eq_add_tsum_ite k]
  simp only [↓reduceIte]
  change (c k+∑' n,aliasRemainder N c k n)-c k = _
  abel

theorem coefficient_samples_error_window (c : (ι → ℤ) → E)
    (hc : Summable (fun n => ‖c n‖)) (K : ℕ) (k : ι → ℤ) (hk : ∀ i, |k i| ≤ K) :
    ‖coefficient N (fun j => synthesis c (fun i => ((j i).val : ℝ)/N)) (frequency N k)-c k‖ ≤
      cubeTail c ((N : ℤ)-K) := by
  rw [coefficient_samples_sub N c hc k]
  apply (norm_tsum_le_tsum_norm (aliasRemainder_summable_norm N c hc k)).trans
  apply Summable.tsum_le_tsum _ (aliasRemainder_summable_norm N c hc k)
    (cubeTail_summable c hc _)
  intro n
  by_cases hnk : n = k
  · simp only [aliasRemainder,hnk,↓reduceIte,norm_zero]
    split_ifs <;> positivity
  · by_cases hm : frequency N n = frequency N k
    · simp only [aliasRemainder,hnk,hm,alias_outside_cube N hk hnk hm,↓reduceIte]
      exact le_rfl
    · simp only [aliasRemainder,hnk,hm,↓reduceIte,norm_zero]
      split_ifs <;> positivity

#print axioms coefficient_samples_error_window

end Maxwell.Continuum.PeriodicSampling.Product
