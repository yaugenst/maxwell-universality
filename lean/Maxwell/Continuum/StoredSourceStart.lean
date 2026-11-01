import Maxwell.Continuum.StoredSourceLoop
import Maxwell.Cost.Structured.WordLiteral
import Maxwell.Cost.WordReplace
import Maxwell.Cost.BankArray.Frame

/-! Source traversal starts by actual cursor reset, archive cloning, and
count loading. Old finite words are scanned and charged. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def startCode : Code := .seq (WordLiteral.code 971 0)
  (.seq (WordReplace.code 508 85) (WordReplace.code 500 972))
def startWork : Finset ℕ := {971,85,972}

theorem start_executes {n : ℕ} (p : Plan n) (gv : ℕ→ℕ) (v : ℕ→Parts)
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
    ∃t,Executes input tape startCode
      ((6*(gv 971).bits.length+11)+((6*oldArchive.length+15*(LogRats.records p.source).length+21)+
        (6*oldCount.length+15*p.source.length.bits.length+21))) s t ∧
      State p 0 (Function.update gv 971 0) v t ∧Word t.val 972 p.source.length ∧
      BinaryPrecision.Frame startWork s.val t.val := by
  obtain ⟨a,e0,index,f0⟩:=WordLiteral.executes 971 0 input tape (gv 971).bits s
    (g.ready.bank 971 (by decide))
  obtain ⟨b,e1,archiveB,f1⟩:=WordReplace.executes 508 85 (by decide) input tape
    (LogRats.records p.source) oldArchive a
    (BankArray.word_of_eq (f0.tapes 508 (by decide)) archive)
    (BankArray.word_of_eq (f0.tapes 85 (by decide)) archiveOld)
  obtain ⟨t,e2,countT,f2⟩:=WordReplace.executes 500 972 (by decide) input tape
    p.source.length.bits oldCount b
    (word_of_eq ((f1.2.2.2.2.2.1 500 (by decide)).trans (f0.tapes 500 (by decide))) count)
    (BankArray.word_of_eq ((f1.2.2.2.2.2.1 972 (by decide)).trans (f0.tapes 972 (by decide))) countOld)
  have frame1 : BinaryPrecision.Frame {85} a.val b.val:=
    ⟨f1.1,f1.2.1,f1.2.2.1,f1.2.2.2.1,f1.2.2.2.2.1,fun i hi=>f1.2.2.2.2.2.1 i (by simpa using hi)⟩
  have frame2 : BinaryPrecision.Frame {972} b.val t.val:=
    ⟨f2.1,f2.2.1,f2.2.2.1,f2.2.2.2.1,f2.2.2.2.2.1,fun i hi=>f2.2.2.2.2.2.1 i (by simpa using hi)⟩
  have frame : BinaryPrecision.Frame startWork s.val t.val:=
    (f0.mono (by decide)).trans ((frame1.mono (by decide)).trans (frame2.mono (by decide)))
  have indexT : Word t.val 971 0:=word_of_eq
    ((frame2.tapes 971 (by decide)).trans (frame1.tapes 971 (by decide))) index
  have keep (i : ℕ) (hi : i∉startWork):=frame.tapes i hi
  have raw : Ready bank v t:=by
    refine ⟨?_,?_⟩
    · intro i hi
      exact word_of_eq (keep i (fun hh=>Finset.disjoint_left.mp (by decide : Disjoint (ids bank) startWork) hi hh)) (ready.1 i hi)
    · intro i hi
      exact blank_of_eq (keep i (by simp only [startWork,Finset.mem_insert,Finset.mem_singleton];omega)) (ready.2 i hi)
  have geometryT : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.constants
      (Function.update gv 971 0) t:=by
    refine ⟨⟨?_,?_,blank_of_eq (keep 7 (by decide)) g.ready.seven⟩,?_,?_,
      BankArray.word_of_eq (keep 962 (by decide)) g.clockWord,?_⟩
    · intro i hi
      by_cases eq : i=971
      · subst i;simpa only [Function.update_self] using indexT
      · rw [Function.update_of_ne eq]
        exact word_of_eq (keep i (by
          simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hi
          simp only [startWork,Finset.mem_insert,Finset.mem_singleton];omega)) (g.ready.bank i hi)
    · exact g.ready.scratch.of_tapes (fun i hi=>keep i (by simp only [startWork,Finset.mem_insert,Finset.mem_singleton];omega))
    · intro i hi
      by_cases eq : i=971
      · subst i;simp
      · simpa only [Function.update_of_ne eq] using g.wordWidth i hi
    · simpa only [frame.memory] using g.array
    · intro i hi
      have neq : i≠971:=by simp only [GeometryOutput.fixedIds,Finset.mem_insert,Finset.mem_singleton] at hi;omega
      simpa only [Function.update_of_ne neq] using g.fixed i hi
  refine ⟨t,by simpa only [startCode,show (0:ℕ).bits.length=0 from rfl,Nat.mul_zero,Nat.add_zero] using e0.seq (e1.seq e2),
    ⟨geometryT,by simp,raw,width,good,scalar,?_,word_of_eq (keep 144 (by decide)) power,
      word_of_eq (keep 4427 (by decide)) precision,BankArray.word_of_eq (keep 992 (by decide)) template,?_,?_⟩,
    countT,frame⟩
  · refine ⟨blank_of_eq (keep 4 (by decide)) clean.1,?_⟩
    intro i hi
    exact blank_of_eq (keep i (fun hh=>Finset.disjoint_left.mp
      (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) startWork) hi hh)) (clean.2 i hi)
  · obtain ⟨origin,word⟩:=archiveB
    refine ⟨origin,?_⟩
    have hh:=(frame2.tapes 85 (by decide)).trans word
    change t.val.tapes 85=BitTape.translate origin (BitTape.ofList (LogRats.records p.source))
    rw [BitTape.translate_ofList]
    exact hh
  · intro i hi
    obtain ⟨xs,hxs,word⟩:=old i hi
    exact ⟨xs,hxs,BankArray.word_of_eq (keep i (by
      simp only [parseWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [startWork,Finset.mem_insert,Finset.mem_singleton];omega)) word⟩

#print axioms start_executes
end Maxwell.Continuum.SourcePayload
