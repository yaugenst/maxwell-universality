import Maxwell.Continuum.PeriodicSamplingReconstruction

/-! Exact reindexing of every congruent Fourier alias by the image
lattice. This is the finite Fourier identity behind periodization. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open scoped Classical

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (N : ℕ) [NeZero N]

def aliasEmbedding (k j : ι → ℤ) : ι → ℤ := fun i => k i+(N : ℤ)*j i

omit [Fintype ι] in
theorem aliasEmbedding_injective (k : ι → ℤ) : Function.Injective (aliasEmbedding N k) := by
  intro a b hab
  funext i
  have hi := congrFun hab i
  dsimp only [aliasEmbedding] at hi
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne N : (N : ℤ) ≠ 0) (add_left_cancel hi)

omit [Fintype ι] [NeZero N] in
theorem aliasEmbedding_frequency (k j : ι → ℤ) :
    frequency N (aliasEmbedding N k j) = frequency N k := by
  funext i
  simp [frequency, aliasEmbedding]

omit [Fintype ι] [NeZero N] in
theorem frequency_eq_iff_image (n k : ι → ℤ) :
    frequency N n = frequency N k ↔ n ∈ Set.range (aliasEmbedding N k) := by
  constructor
  · intro hn
    refine ⟨fun i => (n i-k i)/(N : ℤ), ?_⟩
    funext i
    have hi : ((n i-k i : ℤ) : ZMod N) = 0 := by
      have h := congrFun hn i
      change (n i : ZMod N) = (k i : ZMod N) at h
      push_cast
      rw [h, sub_self]
    have hd : (N : ℤ) ∣ n i-k i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hi
    dsimp only [aliasEmbedding]
    rw [Int.mul_ediv_cancel' hd]
    omega
  · rintro ⟨j, rfl⟩
    exact aliasEmbedding_frequency N k j

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem alias_sum_eq_images (c : (ι → ℤ) → E) (k : ι → ℤ) :
    (∑' n : ι → ℤ, if frequency N n = frequency N k then c n else 0) =
      ∑' j : ι → ℤ, c (aliasEmbedding N k j) := by
  have hi := aliasEmbedding_injective N k
  have hz : ∀ n, n ∉ Set.range (aliasEmbedding N k) →
      (if frequency N n = frequency N k then c n else 0) = 0 := by
    intro n hn
    exact ite_eq_right (fun h => hn ((frequency_eq_iff_image N n k).mp h))
  have hsupport : Function.support (fun n => if frequency N n = frequency N k then c n else 0) ⊆
      Set.range (aliasEmbedding N k) := by
    intro n hn
    by_contra h
    exact hn (hz n h)
  rw [← hi.tsum_eq hsupport]
  apply tsum_congr
  intro j
  rw [ite_eq_left (aliasEmbedding_frequency N k j)]

theorem coefficient_continuous_images (f : C(UnitAddTorus ι, E))
    (hf : Summable (fun n : ι → ℤ => ‖UnitAddTorus.mFourierCoeff f n‖)) (k : ι → ℤ) :
    coefficient N (fun j => f (fun i => ((((j i).val : ℝ)/(N : ℝ) : ℝ) : UnitAddCircle))) (frequency N k) =
      ∑' j : ι → ℤ, UnitAddTorus.mFourierCoeff f (aliasEmbedding N k j) := by
  rw [coefficient_continuous_samples N f hf k, alias_sum_eq_images]

#print axioms coefficient_continuous_images

end Maxwell.Continuum.PeriodicSampling.Product
