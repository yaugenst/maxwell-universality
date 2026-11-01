import Maxwell.Continuum.StoredSourceEntry
import Maxwell.Continuum.StoredGeometryTerminal
import Maxwell.Continuum.StoredGeometryStorageFrame
import Maxwell.Cost.Structured.InputPositions
import Maxwell.Cost.Structured.MemoryFootprint

/-! One complete source record reads its actual packed placement and the
next archived rational, then emits their physical record bytes. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def stepCode : Code := .seq GeometryOutput.terminalStepCode entryCode
def geometryWork : Finset ℕ := Finset.range 10∪{971,976,977,978,987}
def stepWork : Finset ℕ := geometryWork∪entryWork

theorem step_executes {n base slotWidth G : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base slotWidth G clock constants gv s)
    (slotPositive : 0<slotWidth) (slotBound : slotWidth≤G) (hlen : clock.length=slotWidth)
    (hn : n.bits.length≤G) (fits : ∀i,(data.get i).bits.length≤slotWidth)
    (hbase : constants 960=base) (hwidth : constants 961=slotWidth) (hone : constants 970=1)
    (range : gv 971+3≤n)
    (coordinates : ∀j,(GeometryOutput.terminalCoordinate data constants (gv 971) j).bits.length≤G)
    (P B : ℕ) (hB : 2≤B) (hP : (2^P).bits.length≤B) (hprec : P.bits.length≤B)
    (q : ℚ) (v : ℕ→Parts) (width : WidthBank bank B v) (good : Good bank v)
    (qnum : q.num.natAbs.bits.length≤B) (qden : q.den.bits.length≤B)
    (template input : List Bool) (tape : ℕ→Bool) (archiveOrigin : ℤ) (preceding suffix : List Bool)
    (ready : Ready bank v s) (old : WordCleanup.Bounded parseWords B s.val)
    (source : s.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor
      (preceding++(Codec.rat q++suffix)) preceding.length))
    (clean : DyadicFloor.Clean s.val) (power : Word s.val 144 (2^P))
    (precision : Word s.val 4427 P) (stored : BankArray.Word s.val 992 template) :
    ∃cost t w,Executes input tape stepCode cost s t ∧
      cost≤2^30*(G+3)^2+(2^200*(P+B+8)^2+10*template.length) ∧
      t.val.output=(GeometryOutput.terminalBits data constants (gv 971)++
        payloadBits P (numerator P (Function.update v 0 (Parts.literal q))) template).reverse++s.val.output ∧
      GeometryOutput.Context data base slotWidth G clock constants w t ∧w 971=gv 971+3 ∧
      Ready bank (resetValues v) t ∧ WidthBank bank B (resetValues v) ∧ Good bank (resetValues v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      t.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor (preceding++(Codec.rat q++suffix))
        (preceding.length+(Codec.rat q).length)) ∧
      WordCleanup.Bounded parseWords B t.val ∧GeometryOutput.OutputFrame stepWork s.val t.val := by
  obtain ⟨c0,a,w,e0,hc0,ga,index,out0,keep⟩:=GeometryOutput.terminalStep_executes g
    slotPositive slotBound hlen hn fits hbase hwidth hone range coordinates input tape
  have readyA : Ready bank v a:=by
    refine ⟨?_,ga.ready.natural⟩
    intro i hi
    exact word_of_eq (keep i (ids_ge_ten _ _ hi) (fun hm=>Finset.disjoint_left.mp
      (by decide : Disjoint (ids bank) ({971,976,977,978,987}:Finset ℕ)) hi hm)) (ready.1 i hi)
  have oldA : WordCleanup.Bounded parseWords B a.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=old i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (keep i ?_ ?_) word⟩
    all_goals simp only [parseWords,List.mem_cons,List.not_mem_nil,or_false] at hi
    · omega
    · simp only [Finset.mem_insert,Finset.mem_singleton];omega
  have cleanA : DyadicFloor.Clean a.val:=by
    refine ⟨blank_of_eq (e0.protectsTape 4 (by decide +kernel)) clean.1,?_⟩
    intro i hi
    have small : 10 ≤ i ∧ i<960:=by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i small.1 (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (clean.2 i hi)
  obtain ⟨c1,t,e1,hc1,out1,rt,wt,gt,ct,pt,archive,oldT,f1⟩:=entry_executes P B hB hP hprec q v width good
    qnum qden template input tape archiveOrigin preceding suffix a readyA oldA
    ((keep 85 (by decide) (by decide)).trans source) cleanA
    (word_of_eq (keep 144 (by decide) (by decide)) power)
    (word_of_eq (keep 4427 (by decide) (by decide)) precision)
    (BankArray.word_of_eq (keep 992 (by decide) (by decide)) stored)
  have scratch : BankArray.Scratch t.val:=⟨rt.2 0 (by decide),rt.2 1 (by decide),rt.2 2 (by decide),rt.2 3 (by decide),
    blank_of_eq (f1.tapes 5 (by decide)) ga.ready.scratch.2.2.2.2.1,
    blank_of_eq (f1.tapes 6 (by decide)) ga.ready.scratch.2.2.2.2.2.1,
    blank_of_eq (f1.tapes 8 (by decide)) ga.ready.scratch.2.2.2.2.2.2.1,
    blank_of_eq (f1.tapes 9 (by decide)) ga.ready.scratch.2.2.2.2.2.2.2⟩
  have geometryT : GeometryOutput.Context data base slotWidth G clock constants w t:=by
    apply ga.storage_frame f1.memory _ (f1.tapes 962 (by decide)) scratch
      (blank_of_eq (f1.tapes 7 (by decide)) ga.ready.seven)
    intro i hi
    exact f1.tapes i (fun hm=>Finset.disjoint_left.mp (by decide : Disjoint GeometryOutput.ids entryWork) hi hm)
  have positions:=e0.protectsInputPositions (by decide +kernel)
  refine ⟨c0+c1,t,w,e0.seq e1,by omega,?_,geometryT,index,rt,wt,gt,ct,pt,archive,oldT,
    ⟨f1.memory.trans (e0.protectsMemory (by decide +kernel)),f1.inputHead.trans positions.1,
      f1.randomCursor.trans positions.2,?_⟩⟩
  · rw [out1,out0,List.reverse_append,List.append_assoc]
  · intro i hi
    have hi' : i∉geometryWork ∧ i∉entryWork:=by
      simpa only [stepWork,Finset.mem_union,not_or] using hi
    have low : 10 ≤ i:=by
      have hn : i∉Finset.range 10:=fun hh=>hi'.1 (Finset.mem_union_left _ hh)
      simpa only [Finset.mem_range,not_lt] using hn
    exact (f1.tapes i hi'.2).trans (keep i low (fun hh=>hi'.1 (Finset.mem_union_right _ hh)))

#print axioms step_executes
end Maxwell.Continuum.SourcePayload
