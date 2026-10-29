import Maxwell.Cost.HalfPair.Pass

namespace Maxwell.Cost.HalfPair
open Maxwell.Logical.Routing.Coloring
open NumericSplit

theorem array_eq_words (k : ℕ) :
    array k = DoublingPass.words (k+2) (Vector.ofFn (halfSwap (2^k))) := by
  simp only [array,DoublingPass.words,IncidenceEncoding.words,Vector.map_ofFn]
  rfl

/-- The emitted table represents the logical source pairing in the same
arithmetic coordinates used by recursive coloring. -/
theorem array_eq_sourcePair {C R : Type*} (k : ℕ) (index : C × R ≃ Fin (2^k)) :
    array k = DoublingPass.words (k+2)
      (Vector.ofFn ((halfIndex index).permCongr (sourcePair C R))) := by
  rw [← numericPerm_eq_permCongr,numeric_sourcePair]
  exact array_eq_words k

end Maxwell.Cost.HalfPair
