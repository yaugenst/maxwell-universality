import Maxwell.Cost.ChildPermutation.Common
import Maxwell.Cost.BankArray.Decrement

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def widthCode : Code := .seq (.call (WordTransfer.clone 80 120)) (BankArray.decrementCode 120)

/-- The child slot width is calculated by finite binary subtraction. -/
theorem width_executes (width : ℕ) (hwidth : 0<width) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (h80 : Word s.val 80 width.bits) (h120 : Blank s.val 120) :
    ∃ cost t, cost≤44*width.bits.length+49 ∧ Executes input tape widthCode cost s t ∧
      Word t.val 120 (width-1).bits ∧ t.val.memory=s.val.memory ∧
      (∀ i, i≠120 → t.val.tapes i=s.val.tapes i) ∧ BankArray.FrameExcept 120 s.val t.val := by
  obtain ⟨so,hso⟩ := h80
  obtain ⟨origin,ho⟩ := h120
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 80 120 (by omega) input tape width.bits so origin s hso ho
  obtain ⟨dc,d,hdc,ed,dw,dm,dk,df⟩ := BankArray.decrement_bank 120 input tape width.bits
    (by simpa only [addressValue_bits] using hwidth) a ⟨origin,by simp [atapes]⟩
  have keep (i : ℕ) (hi : i≠120) : d.val.tapes i=s.val.tapes i := by
    rw [dk i hi,atapes,Function.update_of_ne hi]
  refine ⟨15*width.bits.length+17+dc,d,by omega,ea.seq ed,by simpa only [addressValue_bits] using dw,
    dm.trans af.2.2.1,keep,?_⟩
  exact ⟨df.1.trans af.2.1,df.2.1.trans af.2.2.2.1,df.2.2.1.trans af.2.2.2.2.1,
    fun i _ hi => keep i hi,
    fun i hi h24 h25 h26 h27 h28 h29 => (df.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
      (af.2.2.2.2.2.2 i h24 h25 h26 h27)⟩

end Maxwell.Cost.ChildPermutation
