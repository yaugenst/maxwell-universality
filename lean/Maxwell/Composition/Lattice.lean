import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Absolute interaction sums on the whole placement lattice. Finite
occupied subsets inherit these bounds without a defect-count multiplier. -/

namespace Maxwell.Composition

abbrev Lattice3 := ℤ × ℤ × ℤ

def latticeDistance (n : Lattice3) : ℕ :=
  n.1.natAbs + n.2.1.natAbs + n.2.2.natAbs

def latticeWeight (ζ : ℝ) (n : Lattice3) : ℝ := ζ ^ latticeDistance n

theorem integer_geometric_hasSum (ζ : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ < 1) :
    HasSum (fun n : ℤ => ζ ^ n.natAbs) ((1 + ζ) / (1 - ζ)) := by
  have hgeom := hasSum_geometric_of_lt_one hζ hζ1
  have hpos : HasSum (fun n : ℕ => ζ ^ (n : ℤ).natAbs) (1 - ζ)⁻¹ := by
    simpa using hgeom
  have hneg : HasSum (fun n : ℕ => ζ ^ (-(n : ℤ)).natAbs) (1 - ζ)⁻¹ := by
    simpa using hgeom
  have hsub : 0 < 1 - ζ := sub_pos.mpr hζ1
  convert HasSum.of_nat_of_neg (f := fun n : ℤ => ζ ^ n.natAbs) hpos hneg using 1
  simp only [Int.natAbs_zero, pow_zero]
  field_simp [hsub.ne']
  ring

set_option maxHeartbeats 2000000 in
theorem lattice_geometric_hasSum (ζ : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ < 1) :
    HasSum (latticeWeight ζ) (((1 + ζ) / (1 - ζ)) ^ 3) := by
  have h := integer_geometric_hasSum ζ hζ hζ1
  have hnonneg : ∀ n : ℤ, 0 ≤ ζ ^ n.natAbs := fun _ => pow_nonneg hζ _
  have htwo : HasSum (fun n : ℤ × ℤ => ζ ^ n.1.natAbs * ζ ^ n.2.natAbs)
      (((1 + ζ) / (1 - ζ)) * ((1 + ζ) / (1 - ζ))) :=
    HasSum.mul (f := fun n : ℤ => ζ ^ n.natAbs)
      (g := fun n : ℤ => ζ ^ n.natAbs) h h
      (Summable.mul_of_nonneg h.summable h.summable hnonneg hnonneg)
  have hthree : HasSum
      (fun n : Lattice3 => ζ ^ n.1.natAbs * (ζ ^ n.2.1.natAbs * ζ ^ n.2.2.natAbs))
      (((1 + ζ) / (1 - ζ)) *
        (((1 + ζ) / (1 - ζ)) * ((1 + ζ) / (1 - ζ)))) :=
    HasSum.mul (f := fun n : ℤ => ζ ^ n.natAbs)
      (g := fun n : ℤ × ℤ => ζ ^ n.1.natAbs * ζ ^ n.2.natAbs) h htwo
      (Summable.mul_of_nonneg h.summable htwo.summable hnonneg
        (fun n => mul_nonneg (hnonneg n.1) (hnonneg n.2)))
  have hvalue : ((1 + ζ) / (1 - ζ)) *
      (((1 + ζ) / (1 - ζ)) * ((1 + ζ) / (1 - ζ))) =
      ((1 + ζ) / (1 - ζ)) ^ 3 := by ring
  rw [hvalue] at hthree
  apply hthree.congr
  intro n
  simp [latticeWeight, latticeDistance, pow_add, mul_assoc]

theorem lattice_sum_bound (ζ : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ < 1)
    (s : Finset Lattice3) :
    ∑ n ∈ s, latticeWeight ζ n ≤ ((1 + ζ) / (1 - ζ)) ^ 3 := by
  have h := lattice_geometric_hasSum ζ hζ hζ1
  exact (Summable.sum_le_tsum s (fun n _ => pow_nonneg hζ _) h.summable).trans_eq h.tsum_eq

theorem lattice_zero_weight (ζ : ℝ) : latticeWeight ζ (0, 0, 0) = 1 := by
  simp [latticeWeight, latticeDistance]

theorem geometric_nonzero_budget (ζ : ℝ) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2) :
    ((1 + ζ) / (1 - ζ)) ^ 3 - 1 ≤ 64 * ζ := by
  have hsub : 0 < 1 - ζ := by linarith
  have hdenpos : 0 < (1 - ζ) ^ 3 := by positivity
  have hden : (1 / 8 : ℝ) ≤ (1 - ζ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - ζ by linarith) 3
    norm_num at h ⊢
    exact h
  have hζ3 : ζ ^ 3 ≤ ζ / 4 := by
    have hsq : ζ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hζ hhalf 2
    have hm := mul_le_mul_of_nonneg_left hsq hζ
    nlinarith
  have hnum : 6 * ζ + 2 * ζ ^ 3 ≤ 8 * ζ := by nlinarith
  have hid : ((1 + ζ) / (1 - ζ)) ^ 3 - 1 =
      (6 * ζ + 2 * ζ ^ 3) / (1 - ζ) ^ 3 := by
    rw [div_pow]
    field_simp [hsub.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hdenpos).mpr
  have hscale := mul_le_mul_of_nonneg_left hden (show 0 ≤ 64 * ζ by positivity)
  nlinarith

theorem lattice_nonzero_sum_bound (ζ : ℝ) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (s : Finset Lattice3) (hzero : (0, 0, 0) ∉ s) :
    ∑ n ∈ s, latticeWeight ζ n ≤ 64 * ζ := by
  have h := lattice_sum_bound ζ hζ (by linarith) (insert (0, 0, 0) s)
  rw [Finset.sum_insert hzero, lattice_zero_weight] at h
  have hb := geometric_nonzero_budget ζ hζ hhalf
  linarith

def nearestLatticeSites : Finset Lattice3 :=
  {(0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 0),
    (0, -1, 0), (0, 0, 1), (0, 0, -1)}

theorem nearest_lattice_sum (ζ : ℝ) :
    ∑ n ∈ nearestLatticeSites, latticeWeight ζ n = 1 + 6 * ζ := by
  simp [nearestLatticeSites, latticeWeight, latticeDistance]
  ring

theorem nearest_lattice_distance (n : Lattice3) (hn : n ∈ nearestLatticeSites) :
    latticeDistance n ≤ 1 := by
  simp only [nearestLatticeSites, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [latticeDistance]

theorem geometric_far_budget (ζ : ℝ) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2) :
    ((1 + ζ) / (1 - ζ)) ^ 3 - 1 - 6 * ζ ≤ 256 * ζ ^ 2 := by
  have hsub : 0 < 1 - ζ := by linarith
  have hdenpos : 0 < (1 - ζ) ^ 3 := by positivity
  have hden : (1 / 8 : ℝ) ≤ (1 - ζ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - ζ by linarith) 3
    norm_num at h ⊢
    exact h
  have hζ4 : ζ ^ 4 ≤ ζ ^ 2 / 4 := by
    have hsq : ζ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hζ hhalf 2
    have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg ζ)
    nlinarith
  have hnum : 18 * ζ ^ 2 - 16 * ζ ^ 3 + 6 * ζ ^ 4 ≤ 32 * ζ ^ 2 := by
    nlinarith [pow_nonneg hζ 3, sq_nonneg ζ]
  have hid : ((1 + ζ) / (1 - ζ)) ^ 3 - 1 - 6 * ζ =
      (18 * ζ ^ 2 - 16 * ζ ^ 3 + 6 * ζ ^ 4) / (1 - ζ) ^ 3 := by
    rw [div_pow]
    field_simp [hsub.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hdenpos).mpr
  have hscale := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 256 * ζ ^ 2 by positivity)
  nlinarith

/-- The total non-nearest interaction weight is quadratic in separation
decay, uniformly over every finite occupied subset of the lattice. -/
theorem lattice_far_sum_bound (ζ : ℝ) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (s : Finset Lattice3) (hfar : ∀ n ∈ s, 2 ≤ latticeDistance n) :
    ∑ n ∈ s, latticeWeight ζ n ≤ 256 * ζ ^ 2 := by
  have hdisjoint : Disjoint s nearestLatticeSites := by
    apply Finset.disjoint_left.mpr
    intro n hs hn
    have hnear := nearest_lattice_distance n hn
    have hfar' := hfar n hs
    omega
  have h := lattice_sum_bound ζ hζ (by linarith) (s ∪ nearestLatticeSites)
  rw [Finset.sum_union hdisjoint, nearest_lattice_sum] at h
  have hb := geometric_far_budget ζ hζ hhalf
  linarith

/-- An injective list of occupied displacements obeys the same whole-lattice
bound. Its length does not appear in the conclusion. -/
theorem occupied_far_weight_bound {ι : Type*} (position : ι → Lattice3)
    (hinj : Function.Injective position) (s : Finset ι)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (hfar : ∀ i ∈ s, 2 ≤ latticeDistance (position i)) :
    ∑ i ∈ s, latticeWeight ζ (position i) ≤ 256 * ζ ^ 2 := by
  classical
  have h := lattice_far_sum_bound ζ hζ hhalf (s.image position) (by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact hfar i hi)
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at h
  exact h

/-- A complete interaction row (or column) with its local couplings removed
is bounded by the geometric tail. This is the interface to the block Schur
estimate, with the actual finite occupied set. -/
theorem occupied_far_row_bound {ι : Type*} [Fintype ι]
    (position : ι → Lattice3) (hinj : Function.Injective position)
    (weight : ι → ℝ) (C ζ : ℝ) (hC : 0 ≤ C)
    (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (hnear : ∀ i, latticeDistance (position i) < 2 → weight i = 0)
    (hweight : ∀ i, weight i ≤ C * latticeWeight ζ (position i)) :
    ∑ i, weight i ≤ C * (256 * ζ ^ 2) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => 2 ≤ latticeDistance (position i)
  have hrestrict : ∑ i, weight i = ∑ i ∈ s, weight i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 2 ≤ latticeDistance (position i)
    · simp [hi]
    · simp [hi, hnear i (by omega)]
  have hfar : ∀ i ∈ s, 2 ≤ latticeDistance (position i) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  calc
    ∑ i, weight i = ∑ i ∈ s, weight i := hrestrict
    _ ≤ ∑ i ∈ s, C * latticeWeight ζ (position i) :=
      Finset.sum_le_sum fun i _ => hweight i
    _ = C * ∑ i ∈ s, latticeWeight ζ (position i) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (256 * ζ ^ 2) :=
      mul_le_mul_of_nonneg_left (occupied_far_weight_bound position hinj s ζ hζ hhalf hfar) hC

end Maxwell.Composition
