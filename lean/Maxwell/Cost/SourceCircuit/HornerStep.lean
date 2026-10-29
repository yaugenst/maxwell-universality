import Maxwell.Cost.SourceCircuit.EmitAccumulator
import Maxwell.Cost.SourceCircuit.WordStack

namespace Maxwell.Cost.SourceCircuit.HornerStep
open Structured
open RationalAccumulator (Blank)

def half : Code := emitAccumulatorCode halfTag [94]
def addLeaf : Code := emitAccumulatorCode additionTag [99,94]
def trueCode : Code :=
  .seq (WordStack.code 103 93 99)
    (.seq addLeaf (.seq (.call (TapeOps.clear 99)) half))
def code : Code := .branch 30 trueCode half
def work : Finset ℕ := {94,95,96,97,99,103}

theorem half_executes (input : List Bool) (tape : ℕ → Bool) (next old gates : List Bool)
    (s : Store) (hs : BankArray.Scratch s.val) (h96 : Blank s.val 96)
    (hn : BankArray.Word s.val 95 next) (ha : BankArray.Word s.val 94 old)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (hlen : old.length = next.length) :
    ∃ cost t, cost ≤ 56*next.length+80 ∧ Executes input tape half cost s t ∧
      BankArray.Word t.val 95 (Increment.bits next) ∧ BankArray.Word t.val 94 next ∧
      Blank t.val 96 ∧ t.val.tapes 97 = BitTape.atEnd (gates ++ halfTag ++ old) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame accumulatorWork s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := emitAccumulator_executes input tape halfTag next old gates [(94,old)]
    s hs h96 hn ha (by intro field hf; simp only [List.mem_singleton] at hf; subst field; exact ⟨by omega,by omega,ha⟩) hg
  refine ⟨cost,t,?_,he,?_⟩
  · simp only [fieldCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      halfTag,List.length_cons,List.length_nil,hlen] at hcost
    omega
  · simpa using ht

theorem addLeaf_executes (input : List Bool) (tape : ℕ → Bool) (next old leaf gates : List Bool)
    (s : Store) (hs : BankArray.Scratch s.val) (h96 : Blank s.val 96)
    (hn : BankArray.Word s.val 95 next) (ha : BankArray.Word s.val 94 old)
    (hl : BankArray.Word s.val 99 leaf) (hg : s.val.tapes 97 = BitTape.atEnd gates)
    (hlen : old.length = next.length) (hleaf : leaf.length = next.length) :
    ∃ cost t, cost ≤ 67*next.length+90 ∧ Executes input tape addLeaf cost s t ∧
      BankArray.Word t.val 95 (Increment.bits next) ∧ BankArray.Word t.val 94 next ∧
      Blank t.val 96 ∧ t.val.tapes 97 = BitTape.atEnd (gates ++ additionTag ++ leaf ++ old) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame accumulatorWork s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := emitAccumulator_executes input tape additionTag next old gates
    [(99,leaf),(94,old)] s hs h96 hn ha (by
      intro field hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl | rfl
      · exact ⟨by omega,by omega,hl⟩
      · exact ⟨by omega,by omega,ha⟩) hg
  refine ⟨cost,t,?_,he,?_⟩
  · simp only [fieldCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      additionTag,List.length_cons,List.length_nil,hlen,hleaf] at hcost
    omega
  · simpa [List.append_assoc] using ht

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem true_executes (input : List Bool) (tape : ℕ → Bool)
    (next old leaf gates lower clock : List Bool) (s : Store)
    (hs : BankArray.Scratch s.val) (h96 : Blank s.val 96) (h99 : Blank s.val 99)
    (hn : BankArray.Word s.val 95 next) (ha : BankArray.Word s.val 94 old)
    (hg : s.val.tapes 97 = BitTape.atEnd gates)
    (hl : s.val.tapes 103 = BitTape.atEnd (lower ++ leaf))
    (hc : BankArray.Word s.val 93 clock)
    (hold : old.length = next.length) (hleaf : leaf.length = next.length)
    (hclock : clock.length = next.length)
    (hroom : addressValue next + 2 < 2 ^ next.length) (hbit : s.val.registers 30 = true) :
    ∃ cost t, cost ≤ 144*next.length+185 ∧ Executes input tape code cost s t ∧
      BankArray.Word t.val 95 (Increment.bits (Increment.bits next)) ∧
      BankArray.Word t.val 94 (Increment.bits next) ∧ Blank t.val 96 ∧ Blank t.val 99 ∧
      t.val.tapes 103 = BitTape.atEnd lower ∧
      t.val.tapes 97 = BitTape.atEnd (gates ++ additionTag ++ leaf ++ old ++ halfTag ++ next) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame work s.val t.val := by
  obtain ⟨leafOrigin,h99⟩ := h99
  obtain ⟨clockOrigin,hc⟩ := hc
  obtain ⟨p,ep,pl,p99,_,_,pm,pf,pk⟩ := WordStack.executes 103 93 99
    (by omega) (by omega) (by omega) input tape leaf lower clock leafOrigin clockOrigin s
    (hclock.trans hleaf.symm) hl h99 hc
  have ps : BankArray.Scratch p.val := scratch_of_tapes hs (fun j hj => pk j (by omega) (by omega))
  obtain ⟨ac,a,hac,ea,an,aa,a96,ag,am,ascratch,af⟩ := addLeaf_executes input tape next old leaf gates p ps
    (RationalAccumulator.blank_of_eq (pk 96 (by omega) (by omega)) h96)
    (BankArray.word_of_eq (pk 95 (by omega) (by omega)) hn)
    (BankArray.word_of_eq (pk 94 (by omega) (by omega)) ha)
    ⟨leafOrigin-leaf.length,p99⟩ ((pk 97 (by omega) (by omega)).trans hg) hold hleaf
  have a99 : a.val.tapes 99 = BitTape.shifted leaf (leafOrigin-leaf.length) :=
    (af.tapes 99 (by omega) (by simp [accumulatorWork])).trans p99
  obtain ⟨c,ec,ct,cf⟩ := WordCall.clear 99 input tape leaf (leafOrigin-leaf.length) a a99
  have cs : BankArray.Scratch c.val := scratch_of_tapes ascratch (by
    intro j hj; simp [ct,show j ≠ 99 by omega])
  have hinc : (Increment.bits next).length = next.length := increment_length next (by omega)
  obtain ⟨hc,t,hct,et,tn,ta,t96,tg,tm,ts,tf⟩ := half_executes input tape (Increment.bits next) next
    (gates ++ additionTag ++ leaf ++ old) c cs
    (RationalAccumulator.blank_of_eq (by simp [ct]) a96)
    (BankArray.word_of_eq (by simp [ct]) an)
    (BankArray.word_of_eq (by simp [ct]) aa)
    (by simpa [ct] using ag) hinc.symm
  have cf' : Frame work a.val c.val := frame_transfer (WordTransfer.frame_of_copy cf) (by
    intro j hj
    have hj99 : j ≠ 99 := by intro he; exact hj (by simp [work,he])
    simp [ct,hj99])
  refine ⟨1+(15*leaf.length+10+(ac+(6*leaf.length+4+hc))),t,?_,
    .yes hbit (ep.seq (ea.seq (ec.seq et))),tn,ta,t96,
    RationalAccumulator.blank_of_eq (tf.tapes 99 (by omega) (by simp [accumulatorWork]))
      ⟨leafOrigin-leaf.length+leaf.length,by simp [ct]⟩,
    ?_,tg,tm.trans (cf.2.2.1.trans (am.trans pm)),ts,
    (pf.mono (by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [work])).trans
      ((af.mono (by simp [accumulatorWork,work])).trans
        (cf'.trans (tf.mono (by simp [accumulatorWork,work]))))⟩
  · rw [hinc] at hct
    omega
  · rw [tf.tapes 103 (by omega) (by simp [accumulatorWork]),ct]
    simp only [Function.update_apply,show (103:ℕ) ≠ 99 by omega,↓reduceIte]
    exact (af.tapes 103 (by omega) (by simp [accumulatorWork])).trans pl

theorem false_executes (input : List Bool) (tape : ℕ → Bool) (next old gates : List Bool)
    (s : Store) (hs : BankArray.Scratch s.val) (h96 : Blank s.val 96)
    (hn : BankArray.Word s.val 95 next) (ha : BankArray.Word s.val 94 old)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (hlen : old.length = next.length)
    (hbit : s.val.registers 30 = false) :
    ∃ cost t, cost ≤ 56*next.length+81 ∧ Executes input tape code cost s t ∧
      BankArray.Word t.val 95 (Increment.bits next) ∧ BankArray.Word t.val 94 next ∧
      Blank t.val 96 ∧ t.val.tapes 97 = BitTape.atEnd (gates ++ halfTag ++ old) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame accumulatorWork s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := half_executes input tape next old gates s hs h96 hn ha hg hlen
  exact ⟨1+cost,t,by omega,.no hbit he,ht⟩

end Maxwell.Cost.SourceCircuit.HornerStep
