import Maxwell.Cost.NormalizedRecordParser.Rational
import Maxwell.Cost.TapeOrigins.Words

/-! The retained rational parser accepts blank result tapes at arbitrary
origins. Its unchanged finite code therefore composes with ordinary charged
cleanup across an unbounded number of source entries. -/
namespace Maxwell.Cost.NormalizedRecordParser
open Structured RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem readRational_shifted_executes (numerator denominator : ℕ)
    (hn10 : numerator≠10) (hn85 : numerator≠85) (hd10 : denominator≠10) (hd85 : denominator≠85)
    (hne : numerator≠denominator)
    (input : List Bool) (tape : ℕ→Bool) (q : ℚ) (archiveOrigin : ℤ) (preceding suffix : List Bool) (s : Store)
    (source : s.val.tapes 85=BitTape.translate archiveOrigin (cursor (preceding++(Codec.rat q++suffix)) preceding.length))
    (counter : Blank s.val 10)
    (numBlank : Blank s.val numerator) (denBlank : Blank s.val denominator):
    ∃cost t,Executes input tape (readRational numerator denominator) cost s t ∧
      cost≤38*(q.num.natAbs.bits.length+q.den.bits.length)+50 ∧
      Word t.val numerator q.num.natAbs ∧Word t.val denominator q.den ∧
      t.val.registers 23=decide (q.num<0) ∧
      t.val.tapes 85=BitTape.translate archiveOrigin (cursor (preceding++(Codec.rat q++suffix)) (preceding.length+(Codec.rat q).length)) ∧
      Blank t.val 10 ∧t.val.inputHead=s.val.inputHead ∧
      Frame {numerator,denominator,85} s.val t.val:=by
  obtain ⟨counterOrigin,counterStored⟩:=counter
  obtain ⟨numOrigin,numStored⟩:=numBlank
  obtain ⟨denOrigin,denStored⟩:=denBlank
  let offset : ℕ→ℤ:=fun i=>if i=10 then counterOrigin else if i=numerator then numOrigin else if i=denominator then denOrigin else if i=85 then archiveOrigin else 0
  let normalized:=s.translateTapes (fun i=>-offset i)
  have originNum : offset numerator=numOrigin:=by simp [offset,hn10]
  have originDen : offset denominator=denOrigin:=by simp [offset,hd10,hne.symm]
  have origin85 : offset 85=archiveOrigin:=by simp [offset,hn85.symm,hd85.symm]
  have origin10 : offset 10=counterOrigin:=by simp [offset]
  have sourceN : normalized.val.tapes 85=cursor (preceding++(Codec.rat q++suffix)) preceding.length:=by
    simp only [normalized,Store.translateTapes,BitRAMState.translateTapes,origin85,source,BitTape.translate_add,add_neg_cancel,BitTape.translate_zero]
  have counterN : normalized.val.tapes 10=BitTape.blank:=by
    simp only [normalized,Store.translateTapes,BitRAMState.translateTapes,origin10,counterStored,
      BitTape.translate,BitTape.blank,add_neg_cancel]
  have numN : normalized.val.tapes numerator=BitTape.blank:=by
    simp only [normalized,Store.translateTapes,BitRAMState.translateTapes,originNum,numStored,
      BitTape.translate,BitTape.blank,add_neg_cancel]
  have denN : normalized.val.tapes denominator=BitTape.blank:=by
    simp only [normalized,Store.translateTapes,BitRAMState.translateTapes,originDen,denStored,
      BitTape.translate,BitTape.blank,add_neg_cancel]
  obtain ⟨cost,u,ex,hc,num,den,sign,su,cu,head,frame⟩:=readRational_executes numerator denominator
    hn10 hn85 hd10 hd85 hne input tape q preceding suffix normalized sourceN counterN numN denN
  let t:=u.translateTapes offset
  have execution:=ex.translateTapes offset
  rw [show normalized.translateTapes offset=s from Store.translateTapes_inverse s offset] at execution
  refine ⟨cost,t,execution,hc,⟨numOrigin,?_⟩,⟨denOrigin,?_⟩,sign,?_,?_,head,?_⟩
  · simp only [t,Store.translateTapes,BitRAMState.translateTapes,num,originNum,BitTape.translate_ofList]
  · simp only [t,Store.translateTapes,BitRAMState.translateTapes,den,originDen,BitTape.translate_ofList]
  · simp only [t,Store.translateTapes,BitRAMState.translateTapes,origin85,su]
  · exact ⟨counterOrigin,by simp only [t,Store.translateTapes,BitRAMState.translateTapes,origin10,cu,
      BitTape.translate_blank]⟩
  · refine ⟨frame.address,frame.memory,frame.randomCursor,frame.output,?_⟩
    intro i hi
    have translated:=congrArg (BitTape.translate (offset i)) (frame.tapes i hi)
    simpa only [t,normalized,Store.translateTapes,BitRAMState.translateTapes,
      BitTape.translate_add,neg_add_cancel,BitTape.translate_zero] using translated

#print axioms readRational_shifted_executes
end Maxwell.Cost.NormalizedRecordParser
