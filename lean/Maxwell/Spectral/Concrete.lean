import Maxwell.Spectral.PeriodicYee
import Maxwell.Certificate.Material
import Mathlib.Analysis.Matrix.PosDef

/-!
# Bind the conventional Yee fiber to the frozen scalar material

The material is the actual 8000-cell integer table and exact integer diamond
predicate imported from the verified data module. The theorems here prove
constitutive bounds and the operator's Hermitian/scalar-shift identities.
They do not assert the unproved finite spectral certificate conclusions.
-/

namespace Maxwell.Spectral.Concrete

open PeriodicYee
open scoped ComplexOrder

noncomputable section

def cellCoordinate (r : Cell20) : Fin 3 → Fin 20 :=
  fun j => ⟨(r j).val, ZMod.val_lt (r j)⟩

def material (r : Cell20) : ℝ :=
  (Maxwell.Certificate.Material.cellValue (cellCoordinate r) : ℝ)

def baseMaterial (r : Cell20) : ℝ :=
  (Maxwell.Certificate.Material.baseValue (cellCoordinate r) : ℝ)

def fiber (k : Momentum) : Matrix Electric20 Electric20 ℂ :=
  PeriodicYee.fiber material k

theorem material_bounds (r : Cell20) : 1 ≤ material r ∧ material r < 13 := by
  unfold material
  exact_mod_cast Maxwell.Certificate.Material.cellValue_bounds (cellCoordinate r)

theorem material_increment_bounds (r : Cell20) :
    0 ≤ material r - baseMaterial r ∧
      material r - baseMaterial r ≤ 1023 / 2 ^ 20 := by
  have hn := Maxwell.Certificate.Material.numerator_bounds
    (cellCoordinate r 0) (cellCoordinate r 1) (cellCoordinate r 2)
  have hnreal : (Maxwell.Certificate.Material.numerator
      (cellCoordinate r 0) (cellCoordinate r 1) (cellCoordinate r 2) : ℝ) ≤ 2046 := by
    exact_mod_cast hn
  have hz : (0 : ℝ) ≤ Maxwell.Certificate.Material.numerator
      (cellCoordinate r 0) (cellCoordinate r 1) (cellCoordinate r 2) := Nat.cast_nonneg _
  dsimp [material, baseMaterial, Maxwell.Certificate.Material.cellValue]
  push_cast
  constructor <;> linarith

theorem material_upper (r : Cell20) : material r ≤ 12 + 1023 / 2 ^ 20 := by
  have hinc := (material_increment_bounds r).2
  have hbase : baseMaterial r ≤ 12 := by
    dsimp [baseMaterial, Maxwell.Certificate.Material.baseValue]
    split <;> norm_num
  linarith

theorem fiber_hermitian (k : Momentum) : (fiber k).IsHermitian :=
  PeriodicYee.fiber_hermitian material k

theorem electric_degree_count : Fintype.card Electric20 = 24000 := electric_count

theorem material_headroom (Ec : ℝ) (hEc : Ec ≤ 957 / 100000) (r : Cell20) :
    material r + 64 * Ec < 25 - 12 := by
  have hm := material_upper r
  linarith

theorem operating_shift (z : ℝ) (k : Momentum) :
    PeriodicYee.fiber (fun c => material c + 64 * z) k =
      fiber k - (z : ℂ) • 1 := PeriodicYee.fiber_uniform_shift material z k

theorem averaged_increment_bounds (e : Electric20) :
    0 ≤ edgeAverage material e - edgeAverage baseMaterial e ∧
      edgeAverage material e - edgeAverage baseMaterial e ≤ 1023 / 2 ^ 20 := by
  have h := edgeAverage_bounds (fun r => material r - baseMaterial r)
    0 (1023 / 2 ^ 20) material_increment_bounds e
  have he : edgeAverage (fun r => material r - baseMaterial r) e =
      edgeAverage material e - edgeAverage baseMaterial e := by
    dsimp [edgeAverage]
    ring
  rwa [he] at h

theorem operator_increment_diagonal (k : Momentum) :
    PeriodicYee.fiber baseMaterial k - fiber k =
      Matrix.diagonal (fun e : Electric20 =>
        (((edgeAverage material e - edgeAverage baseMaterial e) / 64 : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [fiber, PeriodicYee.fiber, mass]
    ring
  · simp [fiber, PeriodicYee.fiber, mass, h]

/-- Concrete nonnegative scalar material perturbation gives the exact
Loewner bounds used in the global spectral comparator. -/
theorem operator_increment_order (k : Momentum) :
    (PeriodicYee.fiber baseMaterial k - fiber k).PosSemidef ∧
      (((1023 / 2 ^ 26 : ℝ) : ℂ) • (1 : Matrix Electric20 Electric20 ℂ) -
        (PeriodicYee.fiber baseMaterial k - fiber k)).PosSemidef := by
  rw [operator_increment_diagonal]
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro e
    apply RCLike.ofReal_nonneg.mpr
    exact div_nonneg (averaged_increment_bounds e).1 (by norm_num)
  · have heq :
        ((1023 / 2 ^ 26 : ℝ) : ℂ) • (1 : Matrix Electric20 Electric20 ℂ) -
          Matrix.diagonal (fun e : Electric20 =>
            (((edgeAverage material e - edgeAverage baseMaterial e) / 64 : ℝ) : ℂ)) =
        Matrix.diagonal (fun e : Electric20 =>
          (((1023 / 2 ^ 26 - (edgeAverage material e - edgeAverage baseMaterial e) / 64 : ℝ)) : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp
      · simp [h]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro e
    apply RCLike.ofReal_nonneg.mpr
    change (0 : ℝ) ≤ 1023 / 2 ^ 26 -
      (edgeAverage material e - edgeAverage baseMaterial e) / 64
    have h := (averaged_increment_bounds e).2
    linarith

end
end Maxwell.Spectral.Concrete
