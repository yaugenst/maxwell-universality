import Maxwell.Cost.PhysicalMaterial.ScatterSpec
import Maxwell.Cost.PhysicalMaterial.DescriptorRead
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open scoped BigOperators

def zeroNums {cells : ℕ} (l : Dense.Layout cells) : Vector (List Bool) cells :=
  Vector.replicate cells (FixedWidth.bits (addressValue l.width) (0:ℕ).bits)
def oneDens {cells : ℕ} (l : Dense.Layout cells) : Vector (List Bool) cells :=
  Vector.replicate cells (FixedWidth.bits (addressValue l.width) (1:ℕ).bits)

private theorem replicate_get {cells : ℕ} (word : List Bool) (x : Fin cells) :
    (Vector.replicate cells word).get x = word := by
  simp [Vector.get,Fin.cast]

private theorem padded_value (width value : ℕ) (h : value.bits.length ≤ width) :
    addressValue (FixedWidth.bits width value.bits) = value := by
  rw [FixedWidth.bits_value _ _ h,addressValue_bits]

/-- Disjoint record supports turn the writes into exactly the physical sum
of defect indicators. Repeated points within one prototype are harmless. -/
theorem filled_value {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (hfit : ∀ i j, (Descriptors.value d i j).bits.length ≤ addressValue l.width)
    (x : Fin cells) (hunique : ∀ i j, x ∈ points.map (locations i) →
      x ∈ points.map (locations j) → i=j) :
    (addressValue ((filledNums d l points locations (zeroNums l) n).get x) : ℚ) /
      addressValue ((filledDens d l points locations (oneDens l) n).get x) =
      ∑ i, if x ∈ points.map (locations i) then
        (Descriptors.value d i 3 : ℚ) / Descriptors.value d i 4 else 0 := by
  classical
  by_cases hex : ∃ i, x ∈ points.map (locations i)
  · obtain ⟨i,hi⟩ := hex
    have unique : ∀ j : Fin n, j≠i → x ∉ points.map (locations j) :=
      fun j hji hj => hji (hunique j i hj hi)
    have hn := filledWords_get_owner (fun j => points.map (locations j))
      (fun j => FixedWidth.bits (addressValue l.width) (Descriptors.value d j 3).bits)
      (zeroNums l) i x hi unique n i.isLt
    have hd := filledWords_get_owner (fun j => points.map (locations j))
      (fun j => FixedWidth.bits (addressValue l.width) (Descriptors.value d j 4).bits)
      (oneDens l) i x hi unique n i.isLt
    change (addressValue ((filledWords _ _ _ n).get x) : ℚ) / addressValue ((filledWords _ _ _ n).get x) = _
    rw [hn,hd,padded_value _ _ (hfit i 3),padded_value _ _ (hfit i 4)]
    symm
    rw [Finset.sum_eq_single i]
    · simp only [hi,ite_true]
    · intro j _ hji
      simp only [unique j hji,ite_false]
    · simp
  · have hnone : ∀ i : Fin n, x ∉ points.map (locations i) := fun i hi => hex ⟨i,hi⟩
    have hn := filledWords_get_none (fun j => points.map (locations j))
      (fun j => FixedWidth.bits (addressValue l.width) (Descriptors.value d j 3).bits)
      (zeroNums l) n x (fun i _ => hnone i)
    have hd := filledWords_get_none (fun j => points.map (locations j))
      (fun j => FixedWidth.bits (addressValue l.width) (Descriptors.value d j 4).bits)
      (oneDens l) n x (fun i _ => hnone i)
    change (addressValue ((filledWords _ _ _ n).get x) : ℚ) / addressValue ((filledWords _ _ _ n).get x) = _
    rw [hn,hd]
    simp only [zeroNums,oneDens,replicate_get]
    rw [padded_value _ 0 (by simp),padded_value _ 1 (by change 1 ≤ addressValue l.width; exact l.width_positive)]
    simp [hnone]

/-- Every emitted denominator is positive, including cells outside all
prototype translates. This fact does not need support disjointness. -/
theorem filled_den_pos {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (hfit : ∀ i, (Descriptors.value d i 4).bits.length ≤ addressValue l.width)
    (hpos : ∀ i, 0 < Descriptors.value d i 4) (x : Fin cells) (k : ℕ) :
    0 < addressValue ((filledDens d l points locations (oneDens l) k).get x) := by
  classical
  change 0 < addressValue ((filledWords _ _ _ k).get x)
  induction k with
  | zero =>
    simp only [filledWords_zero,oneDens,replicate_get]
    rw [padded_value _ 1 (by change 1 ≤ addressValue l.width; exact l.width_positive)]
    decide
  | succ k ih =>
    rw [filledWords]
    split
    · rw [scatterWords_get]
      split
      · rw [padded_value _ _ (hfit _)]
        exact hpos _
      · exact ih
    · exact ih

end Maxwell.Cost.PhysicalMaterial.Scatter
