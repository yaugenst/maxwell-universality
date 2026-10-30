import Maxwell.Continuum.CalibrationRootGridAccumulate
import Mathlib.Algebra.BigOperators.Intervals

/-! Descending countdown order agrees exactly with the full product-grid
DFT. Both real and imaginary sums use every grid point once. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost
set_option maxHeartbeats 2000000

def tailSum (f : ℕ→ℚ) (size remaining : ℕ) : ℚ :=
  ∑k∈Finset.range (size-remaining),f (size-1-k)

theorem tailSum_initial (f : ℕ→ℚ) (size : ℕ) : tailSum f size size=0 := by
  simp [tailSum]

theorem tailSum_step (f : ℕ→ℚ) (size remaining : ℕ) (hr : remaining<size) :
    tailSum f size remaining=tailSum f size (remaining+1)+f remaining := by
  have hd : size-remaining=(size-(remaining+1))+1 := by omega
  have hi : size-1-(size-(remaining+1))=remaining := by omega
  simp only [tailSum,hd,Finset.sum_range_succ,hi]

theorem tailSum_final (f : ℕ→ℚ) (size : ℕ) : tailSum f size 0=∑k∈Finset.range size,f k := by
  simp only [tailSum,Nat.sub_zero]
  exact Finset.sum_range_reflect f size

theorem tailSum_product_grid (grid : ℕ) [NeZero grid] (f : (Fin 3→ZMod grid)→ℚ) :
    tailSum (fun k => f (point grid k)) (grid^3) 0=∑j,f j := by
  rw [tailSum_final,←Fin.sum_univ_eq_sum_range,sum_point]

theorem accumulated_values (S : Finset ℕ) (hS : sumInputs⊆S) (N : ℕ)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hg : Good S (sampleParts N n v)) :
    (accumulated N n v 10).value=(v 10).value+(sampleParts N n v 6).value ∧
    (accumulated N n v 11).value=(v 11).value+(sampleParts N n v 7).value := by
  have h10 := hg 10 (hS (by decide))
  have h11 := hg 11 (hS (by decide))
  have h6 := hg 6 (hS (by decide))
  have h7 := hg 7 (hS (by decide))
  rw [accumulated,accumulate_real,accumulate_imag,Parts.add_value _ _ h10 h6,
    Parts.add_value _ _ h11 h7,sampleParts_other _ _ _ 10 (by omega),sampleParts_other _ _ _ 11 (by omega)]
  exact ⟨rfl,rfl⟩

#print axioms tailSum_product_grid
#print axioms accumulated_values
end Maxwell.Continuum.RationalDataflow.RootGrid
