import Maxwell.Cost.ChildPermutation.PrepareFields

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def prepareCode : Code := .seq widthCode (.seq prepareClockCode (.seq countCode fieldsCode))

def prepareCost (layout : Layout) (k : ℕ) (clock : List Bool) : ℕ :=
  44*layout.parentWidth.bits.length+30*clock.length+15*(2*(2^k)).bits.length+15*layout.colors.bits.length+123

/-- All child metadata are calculated from the parent node's actual tapes:
width subtraction, clock shortening, count halving, and color-address copy. -/
theorem prepare_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (clock : List Bool) (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (s : Store) (before : Before layout clock s.val) (work : Workspace s.val)
    (h96 : Word s.val 96 (2*(2^k)).bits)
    (h120 : Blank s.val 120) (h121 : Blank s.val 121) (h127 : Blank s.val 127)
    (h128 : Blank s.val 128) (h87 : Blank s.val 87) :
    ∃ cost t childClock, cost≤prepareCost layout k clock ∧ Executes input tape prepareCode cost s t ∧
      Config layout [] clock childClock t.val ∧ childClock.length=layout.childWidth ∧
      Word t.val 127 (2^k).bits ∧ Workspace t.val ∧ MetadataFrame s.val t.val := by
  obtain ⟨ac,a,hac,ea,a120,am,ak,af⟩ := width_executes layout.parentWidth (by omega) input tape s before.width h120
  have ma : MetadataFrame s.val a.val := MetadataFrame.of_bank am
    (fun i hi => ak i (by dsimp [MetadataPrivate] at hi; omega)) af
  have ba := before.of_frame ma
  obtain ⟨bc,b,childClock,hbc,eb,b121,hchild,_,bf⟩ := prepare_clock_executes k input tape clock (by omega)
    a ba.clock (RationalAccumulator.blank_of_eq (ak 121 (by omega)) h121)
  have bk (i : ℕ) (hi : i≠121) := bf.2.2.2.2.2.1 i hi hi
  have mb : MetadataFrame a.val b.val := MetadataFrame.of_transfer
    (fun i hi => bk i (by dsimp [MetadataPrivate] at hi; omega)) bf
  obtain ⟨c,ec,c127,cm,ck,cf⟩ := count_executes k input tape b
    (BankArray.word_of_eq ((bk 96 (by omega)).trans (ak 96 (by omega))) h96)
    (RationalAccumulator.blank_of_eq ((bk 127 (by omega)).trans (ak 127 (by omega))) h127)
  have mc : MetadataFrame b.val c.val := MetadataFrame.of_transfer
    (fun i hi => ck i (by dsimp [MetadataPrivate] at hi; omega)) cf
  have bcf := before.of_frame (ma.trans (mb.trans mc))
  obtain ⟨dc,d,hdc,ed,d128,d87,dk,md⟩ := fields_executes layout.colors input tape c bcf.colorBase
    (RationalAccumulator.blank_of_eq ((ck 128 (by omega)).trans ((bk 128 (by omega)).trans (ak 128 (by omega)))) h128)
    (RationalAccumulator.blank_of_eq ((ck 87 (by omega)).trans ((bk 87 (by omega)).trans (ak 87 (by omega)))) h87)
  have frame := ma.trans (mb.trans (mc.trans md))
  have doneBefore := before.of_frame frame
  have d120 := BankArray.word_of_eq ((dk 120 (by omega) (by omega)).trans
    ((ck 120 (by omega)).trans (bk 120 (by omega)))) a120
  have d121 := BankArray.word_of_eq ((dk 121 (by omega) (by omega)).trans (ck 121 (by omega))) b121
  refine ⟨ac+(bc+(15*(2*(2^k)).bits.length+21+dc)),d,childClock,?_,ea.seq (eb.seq (ec.seq ed)),
    ⟨doneBefore.width,doneBefore.index,doneBefore.clock,doneBefore.one,d87,doneBefore.parent,
      d120,d121,doneBefore.bases,d128⟩,by simp only [Layout.childWidth,hw]; omega,
    BankArray.word_of_eq (dk 127 (by omega) (by omega)) c127,frame.workspace work,frame⟩
  dsimp [prepareCost]
  omega

end Maxwell.Cost.ChildPermutation
