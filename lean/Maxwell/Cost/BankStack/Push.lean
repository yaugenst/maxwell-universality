import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.SourceCircuit.WordStack

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- Pad to the actual physical clock, append to the stack, reclaim the pack buffer. -/
def pushCode (source clock stack : ℕ) : Code :=
  .seq (BankArray.packCanonicalCode source clock)
    (.seq (SourceCircuit.appendCode 37 stack) (.call (TapeOps.clear 37)))

theorem push (source clockBank stack : ℕ)
    (hs : 10 ≤ source) (hc : 10 ≤ clockBank) (ha : 10 ≤ stack)
    (ha37 : stack≠37) (input : List Bool) (tape : ℕ → Bool)
    (bits clock preceding : List Bool) (hclock : 0<clock.length) (hfit : bits.length≤clock.length)
    (s : Store) (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hsource : Word s.val source bits) (hclockBank : Word s.val clockBank clock)
    (hstack : s.val.tapes stack=BitTape.atEnd preceding) :
    ∃ cost t, cost≤100*clock.length+110 ∧ Executes input tape (pushCode source clockBank stack) cost s t ∧
      t.val.tapes stack=BitTape.atEnd (preceding++FixedWidth.bits clock.length bits) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {37,stack} s.val t.val := by
  obtain ⟨pc,p,hpc,ep,p37,ps,p7,control,pframe⟩ :=
    BankArray.pack_canonical source clockBank hs hc input tape bits clock hclock hfit s scratch h7 h37 hsource hclockBank
  obtain ⟨po,hp37⟩ := p37
  obtain ⟨a,ea,atapes,aframe⟩ := SourceCircuit.append_executes 37 stack (Ne.symm ha37)
    input tape (FixedWidth.bits clock.length bits) preceding po p hp37
    ((pframe.2.2.2.1 stack (Or.inr ha) ha37).trans hstack)
  obtain ⟨t,et,ttapes,tframe⟩ := WordCall.clear 37 input tape (FixedWidth.bits clock.length bits) po a
    (by simpa only [atapes,Function.update_of_ne (Ne.symm ha37)] using hp37)
  have frame : SourceCircuit.Frame {37,stack} s.val t.val :=
    ((SourceCircuit.frame_except pframe).mono (by intro j hj; simp_all)).trans
      ((SourceCircuit.frame_transfer aframe (fun j hj => by simp_all)).trans
        (SourceCircuit.frame_transfer (WordTransfer.frame_of_copy tframe)
          (fun j hj => by simp_all)))
  have keepSmall (i : ℕ) (hi : i<10) : t.val.tapes i=p.val.tapes i := by
    simp only [ttapes,atapes,Function.update_of_ne (show i≠37 by omega),
      Function.update_of_ne (show i≠stack by omega)]
  refine ⟨pc+(11*(FixedWidth.bits clock.length bits).length+10+
      (6*(FixedWidth.bits clock.length bits).length+4)),t,?_,ep.seq (ea.seq et),?_,
    SourceCircuit.scratch_of_tapes ps keepSmall,
    RationalAccumulator.blank_of_eq (keepSmall 7 (by omega)) p7,
    ⟨po+(FixedWidth.bits clock.length bits).length,by simp [ttapes]⟩,
    tframe.2.2.1.trans (aframe.2.2.1.trans control.2.2.2.1),frame⟩
  · simp only [FixedWidth.bits_length]; omega
  · simp [ttapes,atapes,ha37]

end Maxwell.Cost.BankStack
