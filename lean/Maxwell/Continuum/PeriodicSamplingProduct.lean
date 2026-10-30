import Maxwell.Continuum.PeriodicSamplingTail
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact tensor-product periodic sampling in any finite dimension.
The coefficient formula retains the complete integer alias lattice. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open AddChar
open scoped Classical

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (N : ℕ) [NeZero N]

def character (a j : ι → ZMod N) : ℂ := ∏ i, ZMod.stdAddChar (a i*j i)

theorem character_norm (a j : ι → ZMod N) : ‖character N a j‖ = 1 := by
  simp [character,norm_prod,ZMod.stdAddChar_apply]

theorem character_mul (a b j : ι → ZMod N) :
    character N a j*character N b j = character N (a+b) j := by
  rw [character,character,character,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply,add_mul]

theorem character_sum (a : ι → ZMod N) :
    ∑ j : ι → ZMod N, character N a j =
      if a = 0 then (N : ℂ)^Fintype.card ι else 0 := by
  unfold character
  rw [← Fintype.prod_sum (fun i (j : ZMod N) => ZMod.stdAddChar (a i*j))]
  simp_rw [PeriodicSampling.character_sum]
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    have hi : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def frequency (n : ι → ℤ) : ι → ZMod N := fun i => n i

def phase (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  ∏ i, PeriodicSampling.phase (n i) (x i)

theorem phase_norm (n : ι → ℤ) (x : ι → ℝ) : ‖phase n x‖ = 1 := by
  simp [phase,norm_prod,PeriodicSampling.phase_norm]

def synthesis (c : (ι → ℤ) → E) (x : ι → ℝ) : E := ∑' n, phase n x • c n

def gridSynthesis (c : (ι → ℤ) → E) (j : ι → ZMod N) : E :=
  ∑' n, character N (frequency N n) j • c n

def coefficient (f : (ι → ZMod N) → E) (k : ι → ZMod N) : E :=
  ((N : ℂ)^Fintype.card ι)⁻¹ • ∑ j, character N (-k) j • f j

theorem phase_grid (n : ι → ℤ) (j : ι → ZMod N) :
    phase n (fun i => ((j i).val : ℝ)/N) = character N (frequency N n) j := by
  unfold phase character frequency
  exact Finset.prod_congr rfl (fun i _ => PeriodicSampling.phase_grid N (n i) (j i))

omit [CompleteSpace E] in
theorem synthesis_grid (c : (ι → ℤ) → E) (j : ι → ZMod N) :
    synthesis c (fun i => ((j i).val : ℝ)/N) = gridSynthesis N c j := by
  apply tsum_congr
  intro n
  rw [phase_grid]

theorem weighted_grid_summable (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖))
    (j k : ι → ZMod N) : Summable (fun n =>
      character N (-k) j • (character N (frequency N n) j • c n)) := by
  apply Summable.of_norm_bounded hc
  intro n
  simp only [norm_smul,character_norm,one_mul]
  exact le_rfl

theorem coefficient_gridSynthesis (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖))
    (k : ι → ZMod N) :
    coefficient N (gridSynthesis N c) k =
      ∑' n, if frequency N n = k then c n else 0 := by
  unfold coefficient gridSynthesis
  simp_rw [← tsum_const_smul'']
  rw [← Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (ι → ZMod N))) =>
    weighted_grid_summable N c hc j k)]
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro n
  simp only [smul_smul,character_mul]
  rw [← Finset.sum_smul,character_sum]
  by_cases hn : frequency N n = k
  · simp only [hn,neg_add_cancel,↓reduceIte,smul_smul]
    rw [inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne (N : ℂ))),one_smul]
  · have hs : -k+frequency N n ≠ 0 := by
      intro h
      apply hn
      have he := eq_neg_of_add_eq_zero_right h
      simpa using he
    simp only [hn,hs,↓reduceIte,zero_smul,smul_zero]

theorem coefficient_samples (c : (ι → ℤ) → E) (hc : Summable (fun n => ‖c n‖))
    (k : ι → ℤ) :
    coefficient N (fun j => synthesis c (fun i => ((j i).val : ℝ)/N)) (frequency N k) =
      ∑' n, if frequency N n = frequency N k then c n else 0 := by
  simp_rw [synthesis_grid]
  exact coefficient_gridSynthesis N c hc _

#print axioms coefficient_samples

end Maxwell.Continuum.PeriodicSampling.Product
