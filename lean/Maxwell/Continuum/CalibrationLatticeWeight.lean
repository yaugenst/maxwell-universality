import Maxwell.Continuum.ProfileDecayMajorant
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! An explicit summable majorant on the three-dimensional image
lattice. Its total mass is at most 64, proved by telescoping and finite
product sums. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

def scalarLatticeWeight (j : ℤ) : ℝ := 1/(1+|(j : ℝ)|)^2

theorem scalarLatticeWeight_nonneg (j : ℤ) : 0 ≤ scalarLatticeWeight j := by
  unfold scalarLatticeWeight
  positivity

theorem scalarLatticeWeight_neg_bound (n : ℕ) :
    scalarLatticeWeight (-(n+1 : ℤ)) ≤ 1/((n : ℝ)+1)^2 := by
  simp only [scalarLatticeWeight,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n+1)]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem scalarLatticeWeight_nat_summable : Summable (fun n : ℕ => scalarLatticeWeight n) := by
  simpa [scalarLatticeWeight,add_comm] using Profile.inverse_square_summable

theorem scalarLatticeWeight_neg_summable :
    Summable (fun n : ℕ => scalarLatticeWeight (-(n+1 : ℤ))) :=
  Summable.of_nonneg_of_le (fun _ => scalarLatticeWeight_nonneg _)
    scalarLatticeWeight_neg_bound Profile.inverse_square_summable

theorem scalarLatticeWeight_summable : Summable scalarLatticeWeight := by
  exact Summable.of_nat_of_neg_add_one scalarLatticeWeight_nat_summable scalarLatticeWeight_neg_summable

theorem scalarLatticeWeight_tsum_le : ∑' j : ℤ, scalarLatticeWeight j ≤ 4 := by
  have hp : (∑' n : ℕ,scalarLatticeWeight n) ≤ 2 := by
    simpa [scalarLatticeWeight,add_comm] using Profile.inverse_square_tsum
  have hn : (∑' n : ℕ,scalarLatticeWeight (-(n+1 : ℤ))) ≤ 2 :=
    (scalarLatticeWeight_neg_summable.tsum_le_tsum scalarLatticeWeight_neg_bound
      Profile.inverse_square_summable).trans Profile.inverse_square_tsum
  rw [tsum_of_nat_of_neg_add_one scalarLatticeWeight_nat_summable scalarLatticeWeight_neg_summable]
  linarith

def latticeWeight (j : Fin 3 → ℤ) : ℝ := ∏ i, scalarLatticeWeight (j i)

theorem latticeWeight_nonneg (j : Fin 3 → ℤ) : 0 ≤ latticeWeight j :=
  Finset.prod_nonneg (fun i _ => scalarLatticeWeight_nonneg (j i))

theorem latticeWeight_finset_bound (s : Finset (Fin 3 → ℤ)) :
    ∑ j ∈ s, latticeWeight j ≤ 64 := by
  classical
  let t : Fin 3 → Finset ℤ := fun i => s.image (fun j => j i)
  have hs : s ⊆ Fintype.piFinset t := by
    intro j hj
    simp only [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
  calc
    _ ≤ ∑ j ∈ Fintype.piFinset t, latticeWeight j :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => latticeWeight_nonneg j)
    _ = ∏ i : Fin 3, ∑ n ∈ t i, scalarLatticeWeight n :=
      (Finset.prod_univ_sum t (fun _ n => scalarLatticeWeight n)).symm
    _ ≤ ∏ _i : Fin 3, (4 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun n _ => scalarLatticeWeight_nonneg n)
      · intro i _
        exact (scalarLatticeWeight_summable.sum_le_tsum (t i)
          (fun n _ => scalarLatticeWeight_nonneg n)).trans scalarLatticeWeight_tsum_le
    _ = _ := by norm_num

theorem latticeWeight_summable : Summable latticeWeight :=
  summable_of_sum_le latticeWeight_nonneg latticeWeight_finset_bound

theorem latticeWeight_tsum_le : ∑' j : Fin 3 → ℤ, latticeWeight j ≤ 64 :=
  Real.tsum_le_of_sum_le latticeWeight_nonneg latticeWeight_finset_bound

#print axioms latticeWeight_tsum_le

end Maxwell.Continuum.Calibration
