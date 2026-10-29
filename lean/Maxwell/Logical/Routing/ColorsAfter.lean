import Maxwell.Logical.Routing.DoublingColors
import Mathlib.Data.Nat.Size

/-! The numeric color pass agrees with the existing indexed coloring after
any sufficient number of pointer-doubling rounds, including the binary length
of the token count used by the finite loop implementation. -/

namespace Maxwell.Logical.Routing.ColorsAfter

open Maxwell.Logical.Routing.Doubling

/-- One final numeric comparison pass over the computed minimum array. -/
def colorVector {n : ℕ} (a : Equiv.Perm (Fin n)) (minimum : Vector (Fin n) n) : Vector Bool n :=
  Vector.ofFn (fun i => decide (minimum.get i < minimum.get (a i)))

/-- Any run covering all token positions yields the same indexed colors as
the logarithmic-round specification. No involution assumption is needed here. -/
theorem colorVector_run_eq_indexedColors {n : ℕ} (a b : Equiv.Perm (Fin n))
    (rounds : ℕ) (hsize : n ≤ 2 ^ rounds) :
    colorVector a (run (Equiv.refl (Fin n)) (a * b) rounds).minimum =
      indexedColors (Equiv.refl (Fin n)) a b := by
  apply Vector.ext
  intro i hi
  simp only [colorVector, indexedColors, Vector.getElem_ofFn]
  change decide (minAt (Equiv.refl (Fin n)) (run (Equiv.refl (Fin n)) (a * b) rounds) ⟨i, hi⟩ <
    minAt (Equiv.refl (Fin n)) (run (Equiv.refl (Fin n)) (a * b) rounds) (a ⟨i, hi⟩)) = _
  rw [run_minimum_eq_orbitMin _ _ _ hsize, run_minimum_eq_orbitMin _ _ _ hsize]
  simp only [logarithmic_run_correct]
  rfl

/-- A computed minimum vector may be supplied through its exact array equality. -/
theorem colorVector_eq_indexedColors {n : ℕ} (a b : Equiv.Perm (Fin n))
    (minimum : Vector (Fin n) n) (rounds : ℕ)
    (hminimum : minimum = (run (Equiv.refl (Fin n)) (a * b) rounds).minimum)
    (hsize : n ≤ 2 ^ rounds) :
    colorVector a minimum = indexedColors (Equiv.refl (Fin n)) a b := by
  rw [hminimum]
  exact colorVector_run_eq_indexedColors a b rounds hsize

/-- The binary length is sufficient even for zero tokens. -/
theorem bits_length_covers (n : ℕ) : n ≤ 2 ^ n.bits.length := by
  rw [Nat.size_eq_bits_len]
  exact (Nat.lt_size_self n).le

/-- The finite pointer-loop round count produces exactly the existing colors. -/
theorem colorVector_bits_eq_indexedColors {n : ℕ} (a b : Equiv.Perm (Fin n)) :
    colorVector a (run (Equiv.refl (Fin n)) (a * b) n.bits.length).minimum =
      indexedColors (Equiv.refl (Fin n)) a b :=
  colorVector_run_eq_indexedColors a b n.bits.length (bits_length_covers n)

/-- Equality form for the actual minimum array returned by the finite loop. -/
theorem colorVector_eq_indexedColors_of_bits {n : ℕ} (a b : Equiv.Perm (Fin n))
    (minimum : Vector (Fin n) n)
    (hminimum : minimum = (run (Equiv.refl (Fin n)) (a * b) n.bits.length).minimum) :
    colorVector a minimum = indexedColors (Equiv.refl (Fin n)) a b :=
  colorVector_eq_indexedColors a b minimum n.bits.length hminimum (bits_length_covers n)

end Maxwell.Logical.Routing.ColorsAfter
