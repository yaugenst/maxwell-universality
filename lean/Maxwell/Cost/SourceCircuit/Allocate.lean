import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.Write
import Maxwell.Logical.CopyBank

/-! A concrete allocation step for the copy bank. The root table lives in
bit-addressed memory. Its selected old root is read once, copied into two
gate records, and replaced by the second fresh gate identifier. -/

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def allocationWork : Finset ℕ := {94, 95, 96, 97}

/-- Banks 90/91/92/93 contain width, selected input, array base and width
clock. Bank 95 is the next gate ID; 96 receives the exposed leaf. -/
def allocateCode : Code :=
  .seq (BankArray.readBankCode 90 91 92 93 94)
    (.seq (.call (WordTransfer.clone 95 96))
      (.seq copiesCode
        (.seq (BankArray.incrementCode 95)
          (.seq (BankArray.writeCode 90 91 92 95)
            (.seq (BankArray.incrementCode 95) (.call (TapeOps.clear 94)))))))

def allocationCost (width index base clock : List Bool) : ℕ :=
  2 * BankArray.costCap width index base clock + 83 * addressValue width + 132

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem allocate_executes {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (width index base clock next preceding : List Bool) (roots : Vector (List Bool) n)
    (i : Fin n) (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (hnext : next.length = addressValue width)
    (hroom : addressValue next + 2 < 2 ^ next.length) (s : Store)
    (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h90 : BankArray.Word s.val 90 width) (h91 : BankArray.Word s.val 91 index)
    (h92 : BankArray.Word s.val 92 base) (h93 : BankArray.Word s.val 93 clock)
    (h95 : BankArray.Word s.val 95 next)
    (h97 : s.val.tapes 97 = BitTape.atEnd preceding)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) roots) :
    ∃ cost, ∃ t : Store, cost ≤ allocationCost width index base clock ∧
      Executes input randomTape allocateCode cost s t ∧
      BankArray.Word t.val 95 (Increment.bits (Increment.bits next)) ∧
      BankArray.Word t.val 96 next ∧ Blank t.val 94 ∧ Blank t.val 7 ∧
      t.val.tapes 97 = BitTape.atEnd
        (preceding ++ copyTag ++ roots.get i ++ copyTag ++ roots.get i) ∧
      t.val.memory = MemoryWord.writeBits s.val.memory
        (addressValue base + i.val * addressValue width) (Increment.bits next) ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (roots.set i (Increment.bits next)) ∧
      BankArray.Scratch t.val ∧ Frame allocationWork s.val t.val ∧
      (Increment.bits (Increment.bits next)).length = addressValue width := by
  have hn1 : (Increment.bits next).length = next.length := increment_length next (by omega)
  have hn2 : (Increment.bits (Increment.bits next)).length = next.length := by
    rw [increment_length (Increment.bits next) (by rw [Increment.bits_value,hn1]; omega),hn1]
  have rootlen := harray.length i
  obtain ⟨rc,r,hrc,er,hr94,hrs,hr7,hrm,hra,rf⟩ := BankArray.read_bank 90 91 92 93 94
    (by omega) (by omega) (by omega) (by omega) (by omega)
    input randomTape width index base clock roots i hwidth hindex hclock s
    hscratch h7 h94 h90 h91 h92 h93 harray
  have rf' : Frame allocationWork s.val r.val :=
    (frame_except rf).mono (by simp [allocationWork])
  obtain ⟨nextOrigin,hn⟩ := h95
  obtain ⟨leafOrigin,hl⟩ := h96
  have rn : r.val.tapes 95 = BitTape.shifted next nextOrigin :=
    (rf.2.2.2.1 95 (by omega) (by omega)).trans hn
  have rl : r.val.tapes 96 = {BitTape.blank with head := leafOrigin} :=
    (rf.2.2.2.1 96 (by omega) (by omega)).trans hl
  obtain ⟨c,ec,ct,cf⟩ := WordCall.clone 95 96 (by omega) input randomTape next
    nextOrigin leafOrigin r rn rl
  have cs : BankArray.Scratch c.val := scratch_of_tapes hrs (by
    intro j hj; simp [ct,show j ≠ 96 by omega])
  have cf' : Frame allocationWork r.val c.val := frame_transfer cf (by
    intro j hj; simp only [allocationWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    simp [ct,hj.2.2.1])
  obtain ⟨a,ea,archiveTapes,am,af⟩ := copies_executes input randomTape (roots.get i) preceding c
    (BankArray.word_of_eq (by simp [ct]) hr94)
    (by simpa [ct] using (rf.2.2.2.1 97 (by omega) (by omega)).trans h97)
  have ascratch : BankArray.Scratch a.val := scratch_of_tapes cs (by
    intro j hj; simp [archiveTapes,show j ≠ 97 by omega])
  have af' : Frame allocationWork c.val a.val := af.mono (by simp [allocationWork])
  have an : BankArray.Word a.val 95 next :=
    ⟨nextOrigin,by simp [archiveTapes,ct,rn]⟩
  obtain ⟨ic,u,hic,ei,un,us,um,_,uk,uf⟩ :=
    BankArray.increment_bank 95 (by omega) input randomTape next a an ascratch
  have uf' : Frame allocationWork a.val u.val :=
    (frame_except uf).mono (by simp [allocationWork])
  have su := rf'.trans (cf'.trans (af'.trans uf'))
  have umem : u.val.memory = s.val.memory := um.trans (am.trans (cf.2.2.1.trans hrm))
  obtain ⟨wc,w,hwc,ew,wm,wa,ws,w7,wf⟩ := BankArray.write_bank 90 91 92 95
    (by omega) (by omega) (by omega) (by omega) input randomTape width index base
    (Increment.bits next) roots i hwidth hindex (hn1.trans hnext) u us
    (BankArray.word_of_eq (su.tapes 90 (by omega) (by simp [allocationWork])) h90)
    (BankArray.word_of_eq (su.tapes 91 (by omega) (by simp [allocationWork])) h91)
    (BankArray.word_of_eq (su.tapes 92 (by omega) (by simp [allocationWork])) h92)
    un (by simpa [umem] using harray)
  have wf' : Frame allocationWork u.val w.val := (frame_bank wf).mono (by simp)
  have wn : BankArray.Word w.val 95 (Increment.bits next) :=
    BankArray.word_of_eq (wf.2.2.2.1 95 (by omega)) un
  obtain ⟨jc,v,hjc,ej,vn,vs,vm,_,vk,vf⟩ :=
    BankArray.increment_bank 95 (by omega) input randomTape (Increment.bits next) w wn ws
  have vf' : Frame allocationWork w.val v.val :=
    (frame_except vf).mono (by simp [allocationWork])
  have keep94 : v.val.tapes 94 = r.val.tapes 94 := by
    rw [vf.2.2.2.1 94 (by omega) (by omega),wf.2.2.2.1 94 (by omega),
      uf.2.2.2.1 94 (by omega) (by omega)]
    simp [archiveTapes,ct]
  obtain ⟨parentOrigin,hparent⟩ := hr94
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 94 input randomTape (roots.get i) parentOrigin v
    (keep94.trans hparent)
  have tf' : Frame allocationWork v.val t.val :=
    frame_transfer (WordTransfer.frame_of_copy tf) (by
      intro j hj
      have hj94 : j ≠ 94 := by intro hh; exact hj (by simp [hh,allocationWork])
      simp [tt,hj94])
  have tmem : t.val.memory = w.val.memory := tf.2.2.1.trans vm
  have texec := er.seq (ec.seq (ea.seq (ei.seq (ew.seq (ej.seq et)))))
  refine ⟨_,t,?_,texec,
    BankArray.word_of_eq (by simp [tt]) vn,
    ⟨leafOrigin,?_⟩,
    ⟨parentOrigin+(roots.get i).length,by simp [tt]⟩,
    ?_,?_,?_,?_,?_,rf'.trans (cf'.trans (af'.trans (uf'.trans (wf'.trans (vf'.trans tf'))))),
    hn2.trans hnext⟩
  · have hwc' : wc ≤ BankArray.costCap width index base clock := by
      simpa only [BankArray.costCap,hn1,hnext,← hclock] using hwc
    dsimp [allocationCost]
    rw [hn1] at hjc
    omega
  · rw [tt]
    simp only [Function.update_apply,show (96:ℕ) ≠ 94 by omega,↓reduceIte]
    rw [vf.2.2.2.1 96 (by omega) (by omega),wf.2.2.2.1 96 (by omega),
      uf.2.2.2.1 96 (by omega) (by omega)]
    simp [archiveTapes,ct]
  · apply RationalAccumulator.blank_of_eq (s := r.val) _ hr7
    rw [tt]
    simp only [Function.update_apply,show (7:ℕ) ≠ 94 by omega,↓reduceIte]
    rw [vk 7 (by omega),w7,uk 7 (by omega)]
    simp [archiveTapes,ct]
  · rw [tt]
    simp only [Function.update_apply,show (97:ℕ) ≠ 94 by omega,↓reduceIte]
    rw [vf.2.2.2.1 97 (by omega) (by omega),wf.2.2.2.1 97 (by omega),
      uf.2.2.2.1 97 (by omega) (by omega)]
    simp [archiveTapes]
  · rw [tmem,wm,umem]
  · simpa [tmem] using wa
  · exact scratch_of_tapes vs (by intro j hj; simp [tt,show j ≠ 94 by omega])

end Maxwell.Cost.SourceCircuit
