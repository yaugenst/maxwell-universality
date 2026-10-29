import Maxwell.Cost.BankArray.Common
import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.NormalizeWord

namespace Maxwell.Cost.BankArray
open Structured

def decrementCode (bank : ℕ) : Code :=
  .seq (CountedShifted.test bank) (.call (NormalizeWord.program bank))

/-- Decrement a positive stored natural and canonically trim its binary word.
The counter traversal and both normalization scans are explicitly charged. -/
theorem decrement_bank (bank : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool)
    (hpositive : 0<addressValue bits) (s : Store) (hw : Word s.val bank bits) :
    ∃ cost t, cost≤29*bits.length+32 ∧ Executes input tape (decrementCode bank) cost s t ∧
      Word t.val bank (addressValue bits-1).bits ∧ t.val.memory=s.val.memory ∧
      (∀ i, i≠bank → t.val.tapes i=s.val.tapes i) ∧ FrameExcept bank s.val t.val := by
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨a,ea,aw,_,af⟩ := CountedShifted.test_executes bank origin input tape s bits ho
  obtain ⟨nc,n,hnc,en,hnp,hnw,_,nf⟩ := NormalizeWord.simulation bank origin input tape
    (subtractBit true bits) a.val a.property aw
  have en' : Executes input tape (.call (NormalizeWord.program bank)) (nc+1) a (Store.ofState n) :=
    .call _ a n nc en (by rw [hnp]; rfl)
  have value : addressValue (subtractBit true bits)=addressValue bits-1 := subtractBit_pred bits hpositive
  refine ⟨13*bits.length+14+(nc+1),Store.ofState n,?_,ea.seq en',⟨origin,by simpa only [value,Store.ofState] using hnw⟩,
    nf.2.2.1.trans af.2.2.1,?_,?_⟩
  · rw [subtractBit_length] at hnc
    omega
  · intro i hi
    exact (nf.2.2.2.2.2.1 i hi).trans (af.2.2.2.2.2.1 i hi)
  · refine ⟨nf.2.1.trans af.2.1,nf.2.2.2.1.trans af.2.2.2.1,nf.2.2.2.2.1.trans af.2.2.2.2.1,
      fun i _ hi => (nf.2.2.2.2.2.1 i hi).trans (af.2.2.2.2.2.1 i hi),?_⟩
    intro i hi h24 h25 h26 h27 _ h29
    exact (nf.2.2.2.2.2.2 i h24 h25 h26 h27).trans (af.2.2.2.2.2.2 i (by omega) h24 h25 h29)

end Maxwell.Cost.BankArray
