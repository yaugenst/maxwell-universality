import Maxwell.Cost.ChildPermutation.PrepareCommon
import Maxwell.Cost.PadWord

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def fieldsCode : Code := .seq (.call (WordTransfer.clone 85 128)) (.call (PadWord.program 87))

/-- Retain the actual color-buffer address and install its one-bit read clock. -/
theorem fields_executes (base : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (h85 : Word s.val 85 base.bits) (h128 : Blank s.val 128) (h87 : Blank s.val 87) :
    ∃ cost t, cost≤15*base.bits.length+23 ∧ Executes input tape fieldsCode cost s t ∧
      Word t.val 128 base.bits ∧ Word t.val 87 [false] ∧
      (∀ i, i≠128 → i≠87 → t.val.tapes i=s.val.tapes i) ∧ MetadataFrame s.val t.val := by
  obtain ⟨bo,hbo⟩ := h85
  obtain ⟨origin,ho⟩ := h128
  obtain ⟨clockOrigin,hclock⟩ := h87
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 85 128 (by omega) input tape base.bits bo origin s hbo ho
  have a87 : a.val.tapes 87=BitTape.shifted [] clockOrigin := by simpa [atapes] using hclock
  obtain ⟨pc,hpc,ep,p87,pf⟩ := PadWord.simulation 87 clockOrigin input tape [] a.val a.property a87
  let p := Store.ofState (PadWord.finish 87 a.val [])
  have ep' : Executes input tape (.call (PadWord.program 87)) (pc+1) a p :=
    .call _ a _ pc ep (by simp [PadWord.program,PadWord.finish])
  have keep (i : ℕ) (h128 : i≠128) (h87 : i≠87) : p.val.tapes i=s.val.tapes i := by
    change (PadWord.finish 87 a.val []).tapes i=s.val.tapes i
    rw [pf.2.2.2.2.2.1 i h87 h87,atapes,Function.update_of_ne h128]
  have metaA : MetadataFrame s.val a.val := MetadataFrame.of_transfer
    (fun i hi => by simp [atapes,show i≠128 by dsimp [MetadataPrivate] at hi; omega]) af
  have metaP : MetadataFrame a.val p.val := MetadataFrame.of_transfer
    (fun i hi => pf.2.2.2.2.2.1 i (by dsimp [MetadataPrivate] at hi; omega)
      (by dsimp [MetadataPrivate] at hi; omega)) (WordTransfer.frame_of_copy pf)
  refine ⟨15*base.bits.length+17+(pc+1),p,by omega,ea.seq ep',⟨origin,?_⟩,
    ⟨clockOrigin,by simpa only [p,Store.ofState,PadWord.bits] using p87⟩,keep,metaA.trans metaP⟩
  change (PadWord.finish 87 a.val []).tapes 128=BitTape.shifted base.bits origin
  rw [pf.2.2.2.2.2.1 128 (by omega) (by omega)]
  simp [atapes]

end Maxwell.Cost.ChildPermutation
