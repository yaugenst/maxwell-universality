import Maxwell.Cost.NormalizedRecordParser.Word

/-! Canonical rational wire parsing from a retained work tape. The original
input stream and shared memory are untouched, and both magnitude words are
rewound for arithmetic. The source head advances by the exact record size. -/
namespace Maxwell.Cost.NormalizedRecordParser
open Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def readRational (numerator denominator : ℕ) : Code:=.seq (.call signProgram)
  (.seq (readWord numerator) (readWord denominator))

theorem readRational_executes (numerator denominator : ℕ)
    (hn10 : numerator≠10) (hn85 : numerator≠85) (hd10 : denominator≠10) (hd85 : denominator≠85)
    (hne : numerator≠denominator)
    (input : List Bool) (tape : ℕ→Bool) (q : ℚ) (preceding suffix : List Bool) (s : Store)
    (source : s.val.tapes 85=cursor (preceding++(Codec.rat q++suffix)) preceding.length)
    (counter : s.val.tapes 10=BitTape.blank)
    (numBlank : s.val.tapes numerator=BitTape.blank) (denBlank : s.val.tapes denominator=BitTape.blank) :
    ∃cost t,Executes input tape (readRational numerator denominator) cost s t ∧
      cost≤38*(q.num.natAbs.bits.length+q.den.bits.length)+50 ∧
      t.val.tapes numerator=BitTape.ofList q.num.natAbs.bits ∧
      t.val.tapes denominator=BitTape.ofList q.den.bits ∧
      t.val.registers 23=decide (q.num<0) ∧
      t.val.tapes 85=cursor (preceding++(Codec.rat q++suffix)) (preceding.length+(Codec.rat q).length) ∧
      t.val.tapes 10=BitTape.blank ∧ t.val.inputHead=s.val.inputHead ∧
      Frame {numerator,denominator,85} s.val t.val:=by
  let negative:=decide (q.num<0)
  let beforeNum:=preceding++[negative]
  let beforeDen:=beforeNum++Codec.nat q.num.natAbs
  have bit : (s.val.tapes 85).read=some negative:=by
    rw [source]
    simp [BitTape.read,BitTape.ofList,Codec.rat,Codec.int,negative]
  have e0:=sign_executes input tape negative s bit
  let a:=Store.ofState (signFinish negative s.val)
  have sourceA : a.val.tapes 85=cursor
      (beforeNum++(Codec.nat q.num.natAbs++(Codec.nat q.den++suffix))) beforeNum.length:=by
    simp [a,Store.ofState,signFinish,source,beforeNum,Codec.rat,Codec.int,negative,List.append_assoc]
  have counterA : a.val.tapes 10=BitTape.blank:=by simpa only [a,Store.ofState,signFinish,Function.update_of_ne (by decide : (10:ℕ)≠85)] using counter
  have numA : a.val.tapes numerator=BitTape.blank:=by simpa only [a,Store.ofState,signFinish,Function.update_of_ne hn85] using numBlank
  have denA : a.val.tapes denominator=BitTape.blank:=by simpa only [a,Store.ofState,signFinish,Function.update_of_ne hd85] using denBlank
  obtain ⟨c1,b,e1,h1,sourceB,counterB,numB,headB,signB,f1⟩:=readWord_executes numerator hn10 hn85 input tape
    q.num.natAbs beforeNum (Codec.nat q.den++suffix) a sourceA counterA numA
  have next : b.val.tapes 85=cursor (beforeDen++(Codec.nat q.den++suffix)) beforeDen.length:=by
    simpa [beforeDen,List.append_assoc] using sourceB
  have denB : b.val.tapes denominator=BitTape.blank:=(f1.tapes denominator (by simp [hne.symm,hd85])).trans denA
  obtain ⟨c2,t,e2,h2,sourceT,counterT,denT,headT,signT,f2⟩:=readWord_executes denominator hd10 hd85 input tape
    q.den beforeDen suffix b next counterB denB
  refine ⟨4+(c1+c2),t,e0.seq (e1.seq e2),by omega,
    (f2.tapes numerator (by simp [hne,hn85])).trans numB,denT,?_,?_,counterT,headT.trans headB,?_⟩
  · exact signT.trans (signB.trans (by simp only [a,Store.ofState,signFinish];rfl))
  · simpa [beforeDen,beforeNum,Codec.rat,Codec.int,negative,List.append_assoc,add_assoc,add_left_comm,add_comm] using sourceT
  · have f0 : Frame {85} s.val a.val:=by
      have hh:=sign_frame negative s.val
      exact ⟨hh.address,hh.memory,hh.randomCursor,hh.output,hh.tapes⟩
    exact (f0.mono (show ({85}:Finset ℕ)⊆{numerator,denominator,85} by simp)).trans
      ((f1.mono (show ({numerator,85}:Finset ℕ)⊆{numerator,denominator,85} by simp [Finset.subset_iff])).trans
        (f2.mono (show ({denominator,85}:Finset ℕ)⊆{numerator,denominator,85} by simp [Finset.subset_iff])))

#print axioms readRational_executes
end Maxwell.Cost.NormalizedRecordParser
