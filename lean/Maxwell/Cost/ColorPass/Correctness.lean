import Maxwell.Cost.ColorPass.Loop
import Maxwell.Logical.Routing.ColorsAfter

namespace Maxwell.Cost.ColorPass
open Maxwell.Logical.Routing
open DoublingPass

/-- The original pairing lookup is retained while the minimum vector comes
from the completed numeric doubling run. -/
def comparisonState {n : ℕ} (a b : Equiv.Perm (Fin n)) (rounds : ℕ) : State n :=
  ⟨Vector.ofFn a, (Doubling.run (Equiv.refl (Fin n)) (a*b) rounds).minimum⟩

theorem colors_comparisonState {n : ℕ} (a b : Equiv.Perm (Fin n))
    (rounds : ℕ) (hs : n ≤ 2^rounds) :
    colors (comparisonState a b rounds) = Doubling.indexedColors (Equiv.refl (Fin n)) a b := by
  have he : colors (comparisonState a b rounds) =
      ColorsAfter.colorVector a (Doubling.run (Equiv.refl (Fin n)) (a*b) rounds).minimum := by
    apply Vector.ext
    intro i hi
    simp [colors, bit, comparisonState, ColorsAfter.colorVector, Vector.get, Fin.cast]
  rw [he]
  exact ColorsAfter.colorVector_run_eq_indexedColors a b rounds hs

theorem colors_bits {n : ℕ} (a b : Equiv.Perm (Fin n)) :
    colors (comparisonState a b n.bits.length) = Doubling.indexedColors (Equiv.refl (Fin n)) a b :=
  colors_comparisonState a b n.bits.length (ColorsAfter.bits_length_covers n)

end Maxwell.Cost.ColorPass
