import Maxwell.Continuum.PeriodicSamplingReconstruction

/-! Uniform finite Fourier truncation and coefficient-rounding bounds
for actual continuous functions on the three-dimensional torus. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open UnitAddTorus
open scoped Classical

theorem cubeTail_mono {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖)) {R S : ℤ} (hRS : R ≤ S) :
    cubeTail c S ≤ cubeTail c R := by
  apply (cubeTail_summable c hc S).tsum_le_tsum _ (cubeTail_summable c hc R)
  intro n
  by_cases hS : ∃ i, S ≤ |n i|
  · have hR : ∃ i, R ≤ |n i| := by obtain ⟨i, hi⟩ := hS; exact ⟨i, hRS.trans hi⟩
    simp only [hS, hR, ↓reduceIte, le_refl]
  · simp only [hS, ↓reduceIte]
    split_ifs <;> positivity

def frequencyCube (R : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(R : ℤ)) (R : ℤ))

theorem mem_frequencyCube (R : ℕ) (n : Fin 3 → ℤ) :
    n ∈ frequencyCube R ↔ ∀ i, |n i| ≤ (R : ℤ) := by
  simp only [frequencyCube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem not_mem_frequencyCube (R : ℕ) (n : Fin 3 → ℤ) :
    n ∉ frequencyCube R ↔ ∃ i, ((R+1 : ℕ) : ℤ) ≤ |n i| := by
  rw [mem_frequencyCube, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by omega⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by omega⟩

def polynomial (c : (Fin 3 → ℤ) → ℂ) (R : ℕ) (x : UnitAddTorus (Fin 3)) : ℂ :=
  ∑ n ∈ frequencyCube R, mFourier n x*c n

theorem polynomial_error (f : C(UnitAddTorus (Fin 3), ℂ))
    (hf : Summable (fun n : Fin 3 → ℤ => ‖mFourierCoeff f n‖)) (R : ℕ)
    (x : UnitAddTorus (Fin 3)) :
    ‖f x-polynomial (mFourierCoeff f) R x‖ ≤ cubeTail (mFourierCoeff f) ((R+1 : ℕ) : ℤ) := by
  let c : (Fin 3 → ℤ) → ℂ := fun n => mFourier n x*mFourierCoeff f n
  have hn : Summable (fun n => ‖c n‖) := by
    simpa only [c, norm_mul, monomial_norm, one_mul] using hf
  have he := hn.of_norm.sum_add_tsum_compl (s := frequencyCube R)
  have hrec : (∑' n, c n) = f x := reconstruction f hf x
  rw [hrec] at he
  have ht : f x-polynomial (mFourierCoeff f) R x =
      ∑' n : ↑((frequencyCube R : Set (Fin 3 → ℤ))ᶜ), c n := by
    change f x-(∑ n ∈ frequencyCube R, c n) = _
    rw [← he]
    abel
  rw [ht]
  apply (norm_tsum_le_tsum_norm (hn.subtype _)).trans_eq
  rw [tsum_subtype ((frequencyCube R : Set (Fin 3 → ℤ))ᶜ) (fun n => ‖c n‖)]
  unfold cubeTail
  apply tsum_congr
  intro n
  simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, not_mem_frequencyCube, c, norm_mul,
    monomial_norm, one_mul]
  by_cases h : ∃ i, ((R+1 : ℕ) : ℤ) ≤ |n i| <;> simp only [h, ↓reduceIte]

theorem polynomial_rounding_error (c d : (Fin 3 → ℤ) → ℂ) (R : ℕ) (ε : ℝ)
    (hd : ∀ n ∈ frequencyCube R, ‖c n-d n‖ ≤ ε) (x : UnitAddTorus (Fin 3)) :
    ‖polynomial c R x-polynomial d R x‖ ≤ ((frequencyCube R).card : ℝ)*ε := by
  rw [polynomial, polynomial, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ frequencyCube R, ‖mFourier n x*c n-mFourier n x*d n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ frequencyCube R, ε := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [← mul_sub, norm_mul, monomial_norm, one_mul] using hd n hn
    _ = _ := by simp

theorem frequencyCube_card (R : ℕ) : (frequencyCube R).card = (2*R+1)^3 := by
  simp only [frequencyCube, Fintype.card_piFinset, Int.card_Icc, sub_neg_eq_add,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

#print axioms polynomial_error
#print axioms polynomial_rounding_error

end Maxwell.Continuum.PeriodicSampling.Product
