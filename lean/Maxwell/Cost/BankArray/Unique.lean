import Maxwell.Cost.BankArray.Common

/-! Stored word contents are unique even when their tape origin is existential. -/
namespace Maxwell.Cost.BankArray

theorem word_unique {s : BitRAMState} {i : ℕ} {xs ys : List Bool}
    (hx : BankArray.Word s i xs) (hy : BankArray.Word s i ys) : xs=ys := by
  obtain ⟨ox,hx⟩ := hx
  obtain ⟨oy,hy⟩ := hy
  have he := hx.symm.trans hy
  have ho : ox=oy := congrArg BitTape.head he
  subst oy
  apply List.ext_getElem?
  intro k
  have hk := congrArg (fun z : BitTape => z.cells (ox+k)) he
  simpa [BitTape.shifted] using hk

theorem word_recover {s t : BitRAMState} {i n : ℕ} {xs : List Bool}
    (hn : RationalAccumulator.Word s i n) (hx : BankArray.Word s i xs)
    (hy : BankArray.Word t i xs) : RationalAccumulator.Word t i n := by
  have he := word_unique hn hx
  rw [←he] at hy
  exact hy

#print axioms word_unique
#print axioms word_recover
end Maxwell.Cost.BankArray
