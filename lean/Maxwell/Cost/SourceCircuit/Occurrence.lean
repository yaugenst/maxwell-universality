import Maxwell.Cost.SourceCircuit.Allocate

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def occurrenceWork : Finset ℕ := {94,95,96,97,98}

/-- Retain each exposed copy leaf in its preorder occurrence stream, then
reclaim the temporary leaf bank before processing the next coefficient bit. -/
def occurrenceCode : Code :=
  .seq allocateCode (.seq (appendCode 96 98) (.call (TapeOps.clear 96)))

def occurrenceCost (width index base clock : List Bool) : ℕ :=
  allocationCost width index base clock + 17 * addressValue width + 14

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem occurrence_executes {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (width index base clock next gates leaves : List Bool) (roots : Vector (List Bool) n)
    (i : Fin n) (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (hnext : next.length = addressValue width)
    (hroom : addressValue next + 2 < 2 ^ next.length) (s : Store)
    (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h90 : BankArray.Word s.val 90 width) (h91 : BankArray.Word s.val 91 index)
    (h92 : BankArray.Word s.val 92 base) (h93 : BankArray.Word s.val 93 clock)
    (h95 : BankArray.Word s.val 95 next)
    (h97 : s.val.tapes 97 = BitTape.atEnd gates) (h98 : s.val.tapes 98 = BitTape.atEnd leaves)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) roots) :
    ∃ cost, ∃ t : Store, cost ≤ occurrenceCost width index base clock ∧
      Executes input randomTape occurrenceCode cost s t ∧
      BankArray.Word t.val 95 (Increment.bits (Increment.bits next)) ∧
      Blank t.val 94 ∧ Blank t.val 96 ∧ Blank t.val 7 ∧
      t.val.tapes 97 = BitTape.atEnd
        (gates ++ copyTag ++ roots.get i ++ copyTag ++ roots.get i) ∧
      t.val.tapes 98 = BitTape.atEnd (leaves ++ next) ∧
      t.val.memory = MemoryWord.writeBits s.val.memory
        (addressValue base + i.val * addressValue width) (Increment.bits next) ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (roots.set i (Increment.bits next)) ∧
      BankArray.Scratch t.val ∧ Frame occurrenceWork s.val t.val ∧
      (Increment.bits (Increment.bits next)).length = addressValue width := by
  obtain ⟨ac,a,hac,ea,an,al,a94,a7,a97,am,aa,ascratch,af,alen⟩ :=
    allocate_executes input randomTape width index base clock next gates roots i hwidth hindex
      hclock hnext hroom s hscratch h7 h94 h96 h90 h91 h92 h93 h95 h97 harray
  obtain ⟨origin,hl⟩ := al
  obtain ⟨l,el,lt,lf⟩ := append_executes 96 98 (by omega) input randomTape next leaves origin a hl
    ((af.tapes 98 (by omega) (by simp [allocationWork])).trans h98)
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 96 input randomTape next origin l (by simpa [lt] using hl)
  have tapes : t.val.tapes = Function.update (Function.update a.val.tapes 98
      (BitTape.atEnd (leaves ++ next))) 96 {BitTape.blank with head := origin+next.length} := by
    rw [tt,lt]
  have keep (j : ℕ) (h96 : j ≠ 96) (h98 : j ≠ 98) : t.val.tapes j = a.val.tapes j := by
    simp [tapes,h96,h98]
  have lf' : Frame occurrenceWork a.val l.val := frame_transfer lf (by
    intro j hj
    have hj98 : j ≠ 98 := by intro h; exact hj (by simp [occurrenceWork,h])
    simp [lt,hj98])
  have tf' : Frame occurrenceWork l.val t.val := frame_transfer (WordTransfer.frame_of_copy tf) (by
    intro j hj
    have hj96 : j ≠ 96 := by intro h; exact hj (by simp [occurrenceWork,h])
    simp [tt,hj96])
  have mem : t.val.memory = a.val.memory := tf.2.2.1.trans lf.2.2.1
  refine ⟨_,t,?_,ea.seq (el.seq et),BankArray.word_of_eq (keep 95 (by omega) (by omega)) an,
    RationalAccumulator.blank_of_eq (keep 94 (by omega) (by omega)) a94,
    ⟨origin+next.length,by simp [tapes]⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by omega) (by omega)) a7,
    (keep 97 (by omega) (by omega)).trans a97,by simp [tapes],mem.trans am,
    by simpa [mem] using aa,
    scratch_of_tapes ascratch (by intro j hj; exact keep j (by omega) (by omega)),
    (af.mono (by simp [allocationWork,occurrenceWork])).trans (lf'.trans tf'),alen⟩
  dsimp [occurrenceCost]
  omega

end Maxwell.Cost.SourceCircuit
