import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Counting the low-frequency integer modes of a rectangular PEC box

This file proves the integer cutoff and volume estimate used in the finite
spectral-count lemma of `arxiv/si/part2_continuum.tex`.  It counts the explicit
free-mode frequency triples, with two polarization slots per triple.  Binding
this count to the spectrum of the variable-coefficient Maxwell operator also
requires the PEC Fourier decomposition and the transverse Schur argument;
those analytical statements are not assumed or claimed here.
-/

namespace Maxwell.Continuum.ModeCount

open scoped BigOperators

/-- Side lengths of the box, measured in the fixed physical length unit. -/
abbrev BoxLengths := Fin 3 → ℕ

/-- The squared free-space wave number attached to a box Fourier index. -/
noncomputable def freeEigenvalue (N : BoxLengths) (ν : Fin 3 → ℕ) : ℝ :=
  ∑ j : Fin 3, (Real.pi * (ν j : ℝ) / (N j : ℝ)) ^ 2

/-- Every summand is controlled by the complete free eigenvalue. -/
theorem coordinate_sq_le (N : BoxLengths) (ν : Fin 3 → ℕ) (j : Fin 3) :
    (Real.pi * (ν j : ℝ) / (N j : ℝ)) ^ 2 ≤ freeEigenvalue N ν := by
  exact Finset.single_le_sum
    (f := fun i : Fin 3 => (Real.pi * (ν i : ℝ) / (N i : ℝ)) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/-- The cutoff `26` forces each integer index below twice the side length.
The proof uses only `π > 3`, and avoids square roots and numerical evaluation. -/
theorem index_lt_twice_length (N : BoxLengths) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℕ) (hν : freeEigenvalue N ν ≤ 26) (j : Fin 3) :
    ν j < 2 * N j := by
  by_contra h
  have hidx : (2 : ℝ) * (N j : ℝ) ≤ (ν j : ℝ) := by
    exact_mod_cast (Nat.le_of_not_gt h)
  have hlength : (0 : ℝ) < N j := by exact_mod_cast hN j
  have hratio : (2 : ℝ) ≤ (ν j : ℝ) / (N j : ℝ) :=
    (le_div_iff₀ hlength).2 hidx
  have hp : 6 < Real.pi * ((ν j : ℝ) / (N j : ℝ)) := by
    nlinarith [Real.pi_gt_three]
  have hs := (coordinate_sq_le N ν j).trans hν
  rw [mul_div_assoc] at hs
  nlinarith

/-- Finite rectangular set of candidate frequency triples. -/
abbrev FrequencySlots (N : BoxLengths) := (j : Fin 3) → Fin (1 + 2 * N j)

/-- Two slots per frequency overestimate both the generic transverse block
and the single-polarization blocks with one zero index. -/
abbrev PolarizedSlots (N : BoxLengths) := Fin 2 × FrequencySlots N

/-- The count appearing in the paper before the volume estimate. -/
def spectralCountBudget (N : BoxLengths) : ℕ :=
  2 * ∏ j : Fin 3, (1 + 2 * N j)

/-- The integer volume of the box. -/
def boxVolume (N : BoxLengths) : ℕ := ∏ j : Fin 3, N j

theorem card_frequencySlots (N : BoxLengths) :
    Fintype.card (FrequencySlots N) = ∏ j : Fin 3, (1 + 2 * N j) := by
  simp [FrequencySlots, Fintype.card_pi]

theorem card_polarizedSlots (N : BoxLengths) :
    Fintype.card (PolarizedSlots N) = spectralCountBudget N := by
  simp [PolarizedSlots, spectralCountBudget]

/-- The explicit bound `2 ∏ (1 + 2 Nⱼ) ≤ 54 ∏ Nⱼ`. -/
theorem spectralCountBudget_le_volume (N : BoxLengths) (hN : ∀ j, 0 < N j) :
    spectralCountBudget N ≤ 54 * boxVolume N := by
  have hfactor : ∀ j, 1 + 2 * N j ≤ 3 * N j := fun j => by
    have := hN j
    omega
  have hprod : (∏ j : Fin 3, (1 + 2 * N j)) ≤ ∏ j : Fin 3, (3 * N j) :=
    Finset.prod_le_prod fun j _ => hfactor j
  calc
    spectralCountBudget N ≤ 2 * (∏ j : Fin 3, (3 * N j)) :=
      Nat.mul_le_mul_left 2 hprod
    _ = 54 * boxVolume N := by
      simp [boxVolume, Fin.prod_univ_succ]
      ring

/-- The actual low-free-frequency index set, independent of any chosen finite
bounding rectangle. -/
def LowFrequency (N : BoxLengths) := {ν : Fin 3 → ℕ // freeEigenvalue N ν ≤ 26}

/-- A low-free-frequency triple fits into the explicit finite counting box. -/
noncomputable def lowFrequencyEncoding (N : BoxLengths) (hN : ∀ j, 0 < N j) :
    LowFrequency N ↪ FrequencySlots N where
  toFun ν j := ⟨ν.1 j, by
    have := index_lt_twice_length N hN ν.1 ν.2 j
    omega⟩
  inj' := by
    intro ν μ h
    apply Subtype.ext
    funext j
    exact congrArg Fin.val (congrFun h j)

/-- The free-mode count with two polarization slots is finite, before using
any PDE completeness or spectral theorem. -/
theorem lowFrequency_polarized_card_le (N : BoxLengths) (hN : ∀ j, 0 < N j)
    [Fintype (LowFrequency N)] :
    Fintype.card (Fin 2 × LowFrequency N) ≤ spectralCountBudget N := by
  rw [Fintype.card_prod, Fintype.card_fin, spectralCountBudget]
  apply Nat.mul_le_mul_left 2
  rw [← card_frequencySlots]
  exact Fintype.card_le_of_injective _ (lowFrequencyEncoding N hN).injective

/-- The low-frequency index set is finite by an explicit injection. -/
theorem finite_lowFrequency (N : BoxLengths) (hN : ∀ j, 0 < N j) :
    Finite (LowFrequency N) :=
  Finite.of_injective _ (lowFrequencyEncoding N hN).injective

#print axioms index_lt_twice_length
#print axioms spectralCountBudget_le_volume
#print axioms lowFrequency_polarized_card_le

end Maxwell.Continuum.ModeCount
