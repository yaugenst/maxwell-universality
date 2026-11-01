import Maxwell.Continuum.StoredSourceSetup
import Maxwell.Continuum.StoredSourceStream

/-! Source setup and complete serialization form one fixed program.
The entry bank is the actual post-well bank, including its last numerator. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def completeCode : Code:=.seq setupCode streamCode
def completeWork : Finset ℕ:=setupWork∪streamWork

theorem complete_executes {n : ℕ} (p : Plan n) (N D B H : ℕ) (hB : 2≤B) (hN : 0<N) (hD : 0<D)
    (numWidth : N.bits.length≤B) (denWidth : D.bits.length≤B) (bankBound : 16*(B+1)≤p.bankWidth)
    (gv : ℕ→ℕ) (v : ℕ→Parts) (last : Parts) (canonical : v 0=Parts.literal 0)
    (width : WidthBank bank B (Function.update v 0 last)) (good : Good bank v) (mode : (v 1).value≠0)
    (scalar : ((v 4).value/(v 1).value)/((N:ℚ)/D)=p.scalar)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (g : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.constants gv s)
    (ready : Ready bank (Function.update v 0 last) s) (clean : DyadicFloor.Clean s.val)
    (num : Word s.val 506 N) (den : Word s.val 507 D) (precision : Word s.val 4427 p.precision)
    (powerOld : WordCleanup.Bounded [4808,144] H s.val)
    (template : BankArray.Word s.val 992 p.template)
    (archive : BankArray.Word s.val 508 (LogRats.records p.source))
    (count : Word s.val 500 p.source.length)
    (oldArchive oldCount : List Bool)
    (archiveOld : BankArray.Word s.val 85 oldArchive) (countOld : BankArray.Word s.val 972 oldCount)
    (old : WordCleanup.Bounded parseWords p.bankWidth s.val) :
    ∃cost t gv' v',Executes input tape completeCode cost s t ∧
      cost≤setupCost p.precision B H+
        (((6*(gv 971).bits.length+11)+((6*oldArchive.length+15*(LogRats.records p.source).length+21)+
          (6*oldCount.length+15*p.source.length.bits.length+21)))+
          (20*p.source.length.bits.length+24)+
          ((p.source.length+1)*(13*p.source.length.bits.length+15)+p.source.length*stepCost p)) ∧
      State p p.source.length gv' v' t ∧
      t.val.output=(streamBits p).reverse++s.val.output ∧
      GeometryOutput.OutputFrame completeWork s.val t.val ∧
      WordCleanup.Bounded [972] p.source.length.bits.length t.val:=by
  obtain ⟨c0,a,e0,hc0,ra,ga,wa,ca,power,_,f0⟩:=setup_executes N D p.precision B H hB hN hD numWidth denWidth v last
    canonical width good mode input tape s ready clean num den precision powerOld
  have scratch : BankArray.Scratch a.val:=⟨ra.2 0 (by decide),ra.2 1 (by decide),ra.2 2 (by decide),ra.2 3 (by decide),
    blank_of_eq (f0.tapes 5 (by decide)) g.ready.scratch.2.2.2.2.1,
    blank_of_eq (f0.tapes 6 (by decide)) g.ready.scratch.2.2.2.2.2.1,
    blank_of_eq (f0.tapes 8 (by decide)) g.ready.scratch.2.2.2.2.2.2.1,
    blank_of_eq (f0.tapes 9 (by decide)) g.ready.scratch.2.2.2.2.2.2.2⟩
  have geomA : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.constants gv a:=by
    apply g.storage_frame f0.memory _ (f0.tapes 962 (by decide)) scratch
      (blank_of_eq (f0.tapes 7 (by decide)) g.ready.seven)
    intro i hi
    exact f0.tapes i (fun hh=>Finset.disjoint_left.mp (by decide : Disjoint GeometryOutput.ids setupWork) hi hh)
  have oldA : WordCleanup.Bounded parseWords p.bankWidth a.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=old i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i ?_) word⟩
    simp only [parseWords,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  obtain ⟨c1,t,gv',v',e1,hc1,st,out,f1,counter⟩:=stream_executes p gv (multiplierValues N D v) input tape a geomA ra
    (wa.mono bankBound) ga ((multiplier_value N D v good mode hN hD).trans scalar) ca power
    (word_of_eq (f0.tapes 4427 (by decide)) precision)
    (BankArray.word_of_eq (f0.tapes 992 (by decide)) template)
    (BankArray.word_of_eq (f0.tapes 508 (by decide)) archive)
    (word_of_eq (f0.tapes 500 (by decide)) count) oldArchive oldCount
    (BankArray.word_of_eq (f0.tapes 85 (by decide)) archiveOld)
    (BankArray.word_of_eq (f0.tapes 972 (by decide)) countOld) oldA
  refine ⟨c0+c1,t,gv',v',e0.seq e1,by omega,st,by rw [out,f0.output],
    ⟨f1.memory.trans f0.memory,f1.inputHead.trans f0.inputHead,f1.randomCursor.trans f0.randomCursor,?_⟩,counter⟩
  intro i hi
  have hh : i∉setupWork ∧i∉streamWork:=by simpa only [completeWork,Finset.mem_union,not_or] using hi
  exact (f1.tapes i hh.2).trans (f0.tapes i hh.1)

#print axioms complete_executes
end Maxwell.Continuum.SourcePayload
