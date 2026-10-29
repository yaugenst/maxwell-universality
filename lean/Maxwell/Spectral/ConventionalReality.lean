import Maxwell.Spectral.ConventionalAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The actual conventional-cell fiber is entrywise real at every TRIM. -/
namespace Maxwell.Spectral.ConventionalAnalytic
open Maxwell.Spectral.PeriodicYee
noncomputable section

def trim (k : Direction → ℤ) : Momentum := fun j => Real.pi * (k j : ℝ)

theorem trim_exp (k : Direction → ℤ) (j : Direction) :
    Complex.exp (Complex.I * ((trim k j : ℝ) : ℂ)) = (-1 : ℂ)^(k j) := by
  have he : Complex.I * ((trim k j : ℝ) : ℂ) = (k j : ℂ) * (Real.pi * Complex.I) := by
    simp only [trim, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem boundaryPhase_trim_real (k : Direction → ℤ) (j : Direction) (r : Cell20) :
    star (PeriodicYee.boundaryPhase (trim k) j r) = PeriodicYee.boundaryPhase (trim k) j r := by
  unfold PeriodicYee.boundaryPhase
  split_ifs <;> simp [trim_exp]

theorem difference_trim_real (k : Direction → ℤ) (j : Direction) (r s : Cell20) :
    star (PeriodicYee.difference (trim k) j r s) = PeriodicYee.difference (trim k) j r s := by
  unfold PeriodicYee.difference
  split_ifs <;> simp [boundaryPhase_trim_real]

theorem curl_trim_real (k : Direction → ℤ) (i j : Electric20) :
    star (PeriodicYee.curl (trim k) i j) = PeriodicYee.curl (trim k) i j := by
  unfold PeriodicYee.curl
  split_ifs <;> simp [difference_trim_real]

private theorem gram_real {ι κ : Type*} [Fintype κ]
    (A : Matrix κ ι ℂ) (hA : ∀ i j, star (A i j) = A i j) :
    ∀ i j, star ((A.conjTranspose * A) i j) = (A.conjTranspose * A) i j := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul, hA]
  congr 1
  funext x
  ring

private theorem subtract_real_diagonal {ι : Type*} [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, star (A i j) = A i j) (d : ι → ℝ) (c : ℝ) :
    ∀ i j, star ((A - (c : ℂ) • Matrix.diagonal (fun i => (d i : ℂ))) i j) =
      (A - (c : ℂ) • Matrix.diagonal (fun i => (d i : ℂ))) i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, hA]
  · simp [Matrix.diagonal, hA, hij]

/-- This includes the selected conventional corner (π,π,−π), without an
unproved symmetry transfer between different primitive certificate points. -/
theorem fiber_trim_real (material : Cell20 → ℝ) (k : Direction → ℤ) :
    ∀ i j, star (PeriodicYee.fiber material (trim k) i j) =
      PeriodicYee.fiber material (trim k) i j := by
  have h := subtract_real_diagonal
    ((PeriodicYee.curl (trim k)).conjTranspose * PeriodicYee.curl (trim k))
    (gram_real _ (curl_trim_real k)) (edgeAverage material) (1/64)
  convert h using 1
  norm_num [PeriodicYee.fiber, PeriodicYee.mass]

end
end Maxwell.Spectral.ConventionalAnalytic
