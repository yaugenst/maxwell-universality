import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.PositiveGraph.Metadata
open Structured
open RationalAccumulator (Word Blank)

def clockCode : Code := .seq (.call (WordTransfer.clone 93 146))
  (.seq (.call (ScanForward.program 146))
    (.seq (BinaryPrecision.writeCode 146 [false,false,false]) (.call (Rewind.program 146))))

/-- Extend the actual compiler clock by three physical tape cells. -/
theorem clock (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (origin : ℤ)
    (s : Store) (h93 : s.val.tapes 93 = BitTape.shifted bits origin) (h146 : Blank s.val 146) :
    ∃ t, Executes input tape clockCode (24*bits.length+58) s t ∧
      BankArray.Word t.val 146 (bits++[false,false,false]) ∧
      BinaryPrecision.Frame {146} s.val t.val := by
  obtain ⟨dest,hdest⟩ := h146
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 93 146 (by decide) input tape bits origin dest s h93 hdest
  have a146 : a.val.tapes 146 = BitTape.shifted bits dest := by simp [atapes]
  have f := ScanForward.shifted_steps 146 dest input tape bits a.val a.property a146
  let b := Store.ofState (ScanForward.finish 146 bits.length a.val)
  have eb : Executes input tape (.call (ScanForward.program 146)) (5*bits.length+4) a b :=
    .call _ _ _ _ f.1 rfl
  obtain ⟨c,ec,hc,fc⟩ := BinaryPrecision.write_executes 146 input tape [false,false,false] bits dest b f.2.1
  have r := WordTransfer.rewind_shifted 146 dest input tape (bits++[false,false,false]) c.val c.property hc
  let t := Store.ofState (Rewind.finishAt 146 dest c.val)
  have et : Executes input tape (.call (Rewind.program 146))
      (4*(bits++[false,false,false]).length+6) c t := .call _ _ _ _ r.1 rfl
  have fa : BinaryPrecision.Frame {146} s.val a.val :=
    ⟨af.1,af.2.1,af.2.2.1,af.2.2.2.1,af.2.2.2.2.1,by
      intro i hi
      have hne : i ≠ 146 := by simpa using hi
      simp [atapes,hne]⟩
  have fb : BinaryPrecision.Frame {146} a.val b.val :=
    ⟨f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,f.2.2.2.2.2.1,f.2.2.2.2.2.2.1,by
      intro i hi
      have hne : i ≠ 146 := by simpa using hi
      exact f.2.2.2.2.2.2.2.1 i hne hne⟩
  have ft : BinaryPrecision.Frame {146} c.val t.val := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro i hi
    have hne : i ≠ 146 := by simpa using hi
    simp [t,Store.ofState,Rewind.finishAt,hne]
  refine ⟨t,?_,⟨dest,r.2⟩,((fa.trans fb).trans fc).trans ft⟩
  convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | simp; omega

end Maxwell.Cost.PositiveGraph.Metadata
