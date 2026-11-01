import Maxwell.Continuum.StoredSourceStart
import Maxwell.Continuum.StoredGeometryEmit

/-! The complete source-list serializer executes startup, the list header,
and every source record. Its entry assumptions are actual stored operands. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def streamCode : Code:=.seq startCode (.seq (EmitNatural.code 500) loopCode)
def streamBits {n : ℕ} (p : Plan n) : List Bool:=Codec.nat p.source.length++rows p 0 p.source.length
def streamWork : Finset ℕ:=startWork∪loopWork

theorem State.emit_frame {n j : ℕ} {p : Plan n} {gv : ℕ→ℕ} {v : ℕ→Parts} {s t : Store}
    (h : State p j gv v s) (f : EmitNatural.Frame s t) : State p j gv v t:=by
  have keep (i : ℕ):=congrFun f.2.2.2.2 i
  refine ⟨h.geometry.of_tapes f.2.2.1 f.2.2.2.2,h.cursor,StoredInteger.ready_emit_frame h.raw f,
    h.width,h.good,h.multiplier,⟨blank_of_eq (keep 4) h.clean.1,fun i hi=>blank_of_eq (keep i) (h.clean.2 i hi)⟩,
    word_of_eq (keep 144) h.power,word_of_eq (keep 4427) h.precision,
    BankArray.word_of_eq (keep 992) h.template,?_,?_⟩
  · obtain ⟨origin,archive⟩:=h.archive
    exact ⟨origin,(keep 85).trans archive⟩
  · intro i hi
    obtain ⟨xs,hxs,word⟩:=h.old i hi
    exact ⟨xs,hxs,BankArray.word_of_eq (keep i) word⟩

theorem stream_executes {n : ℕ} (p : Plan n) (gv : ℕ→ℕ) (v : ℕ→Parts)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (g : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.constants gv s)
    (ready : Ready bank v s) (width : WidthBank bank p.bankWidth v) (good : Good bank v)
    (scalar : (v 13).value=p.scalar) (clean : DyadicFloor.Clean s.val)
    (power : Word s.val 144 (2^p.precision)) (precision : Word s.val 4427 p.precision)
    (template : BankArray.Word s.val 992 p.template)
    (archive : BankArray.Word s.val 508 (LogRats.records p.source))
    (count : Word s.val 500 p.source.length)
    (oldArchive oldCount : List Bool)
    (archiveOld : BankArray.Word s.val 85 oldArchive) (countOld : BankArray.Word s.val 972 oldCount)
    (old : WordCleanup.Bounded parseWords p.bankWidth s.val) :
    ∃cost t gv' v',Executes input tape streamCode cost s t ∧
      cost≤((6*(gv 971).bits.length+11)+((6*oldArchive.length+15*(LogRats.records p.source).length+21)+
        (6*oldCount.length+15*p.source.length.bits.length+21)))+
        (20*p.source.length.bits.length+24)+
        ((p.source.length+1)*(13*p.source.length.bits.length+15)+p.source.length*stepCost p) ∧
      State p p.source.length gv' v' t ∧
      t.val.output=(streamBits p).reverse++s.val.output ∧
      GeometryOutput.OutputFrame streamWork s.val t.val ∧
      WordCleanup.Bounded [972] p.source.length.bits.length t.val:=by
  obtain ⟨a,e0,state,countA,f0⟩:=start_executes p gv v input tape s g ready width good scalar clean power precision
    template archive count oldArchive oldCount archiveOld countOld old
  obtain ⟨origin500,word500⟩:=word_of_eq (f0.tapes 500 (by decide)) count
  obtain ⟨b,e1,out1,f1⟩:=EmitNatural.executes 500 p.source.length origin500 input tape a word500
  have stateB:=state.emit_frame f1
  obtain ⟨origin972,word972⟩:=word_of_eq (congrFun f1.2.2.2.2 972) countA
  obtain ⟨c2,t,last,gv',v',e2,hc2,st,out2,word2,len2,f2⟩:=loop_executes stateB
    (show 0+p.source.length≤p.source.length by omega) input tape p.source.length.bits origin972
    (addressValue_bits _) word972
  refine ⟨_,t,gv',v',e0.seq (e1.seq e2),by omega,by simpa only [Nat.zero_add] using st,?_,
    ⟨f2.memory.trans (f1.2.2.1.trans f0.memory),f2.inputHead.trans (f1.2.1.trans f0.inputHead),
      f2.randomCursor.trans (f1.2.2.2.1.trans f0.randomCursor),?_⟩,?_⟩
  · rw [out2,out1,f0.output]
    simp only [streamBits,List.reverse_append,List.append_assoc]
  · intro i hi
    have hp : i∉startWork ∧i∉loopWork:=by simpa only [streamWork,Finset.mem_union,not_or] using hi
    exact (f2.tapes i hp.2).trans ((congrFun f1.2.2.2.2 i).trans (f0.tapes i hp.1))
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨last,len2.le,⟨origin972,word2⟩⟩

#print axioms stream_executes
end Maxwell.Continuum.SourcePayload
