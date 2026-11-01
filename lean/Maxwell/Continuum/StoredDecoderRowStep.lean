import Maxwell.Continuum.StoredDecoderRowRead

/-! One complete row iteration reads actual storage, emits the canonical
row, clears its finite temporaries, and advances the strength cursor. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def stepCode : Code:=.seq readCode (.seq cleanCode StoredInteger.advanceCode)
def stepWork : Finset ℕ:=Finset.range 10∪readWork∪work∪{728}
def stepCost (B H : ℕ):=2^26*(B+5)^2+cleanCost B H+2^14*(B+3)^2

theorem loaded_kept {n : ℕ} (data : Vector ℕ n) (gv v : ℕ→ℕ) (x : Parts) (i : ℕ)
    (hp : i∉coordinatePorts) (hx : i≠1000):loaded data gv v x i=v i:=by
  simp only [loaded,Function.update_of_ne hx,coordinateValues,ite_eq_right hp]

theorem step_executes {n J base slotWidth G : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base slotWidth G clock constants gv s)
    (slotPositive : 0<slotWidth) (slotBound : slotWidth≤G) (hlen : clock.length=slotWidth)
    (hn : n.bits.length≤G) (fits : ∀i,(data.get i).bits.length≤slotWidth)
    (hbase : constants 960=base) (hwidth : constants 961=slotWidth) (hone : constants 970=1)
    (range : gv 971+3≤n) (a : Table J) (table : a.Ready s)
    (rv : ℕ→Parts) (raw : RationalDataflow.Ready StoredInteger.slots rv s)
    (i : Fin J) (index : Word s.val 728 i.val) (one : Word s.val 727 1)
    (v : ℕ→ℕ) (B H : ℕ) (hB : 2≤B) (hGB : G≤B)
    (bank : NatAssign.Bank ids v s.val) (bound : ∀k∈ids,(v k).bits.length≤B)
    (rawWidth : WidthBank StoredInteger.slots B rv) (metadata : a.MetadataWidth B)
    (indexWidth : i.val.bits.length≤B) (positivePower : 0<v 144) (positiveScale : 0<v 4708)
    (old : WordCleanup.Bounded RationalCanonical.workspace H s.val)
    (input : List Bool) (tape : ℕ→Bool):
    ∃cost t,Executes input tape stepCode cost s t ∧cost≤stepCost B H ∧
      t.val.output=(bits (loaded data gv v (a.get i))).reverse++s.val.output ∧
      GeometryOutput.Context data base slotWidth G clock constants
        (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets false) gv) t ∧
      a.Ready t ∧RationalDataflow.Ready StoredInteger.slots (Function.update rv 0 (a.get i)) t ∧
      WidthBank StoredInteger.slots B (Function.update rv 0 (a.get i)) ∧
      Word t.val 728 (i.val+1) ∧Word t.val 727 1 ∧
      NatAssign.Bank ids (reset (loaded data gv v (a.get i))) t.val ∧
      (∀k∈ids,(reset (loaded data gv v (a.get i)) k).bits.length≤B) ∧
      (∀k∈RationalCanonical.workspace,Blank t.val k) ∧
      GeometryOutput.OutputFrame stepWork s.val t.val:=by
  obtain ⟨c0,u,e0,h0,gu,au,ru,wu,iu,bu,vu,f0⟩:=read_executes g slotPositive slotBound hlen hn fits
    hbase hwidth hone range a table rv raw i index v B hGB bank bound rawWidth metadata indexWidth input tape
  have oldU : WordCleanup.Bounded RationalCanonical.workspace H u.val:=by
    intro k hk
    by_cases small : k<4
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (ru.2 k small)⟩
    obtain ⟨word,hw,stored⟩:=old k hk
    refine ⟨word,hw,BankArray.word_of_eq ?_ stored⟩
    by_cases four : k=4
    · subst k;exact e0.protectsTape 4 (by decide)
    · apply f0.tapes k
      · simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hk;omega
      · simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hk
        simp only [readWork,Finset.mem_insert,Finset.mem_singleton,not_or]
        omega
  obtain ⟨c1,w,e1,h1,out1,bw,zw,clean,fw⟩:=clean_emit (loaded data gv v (a.get i)) B H hB vu
    (by simpa only [loaded_kept data gv v (a.get i) 144 (by decide) (by decide)] using positivePower)
    (by simpa only [loaded_kept data gv v (a.get i) 4708 (by decide) (by decide)] using positiveScale)
    input tape u bu ru.2 oldU
  have gw:=geometry_frame gu fw zw
  have aw:=table_frame au fw zw
  have rw : RationalDataflow.Ready StoredInteger.slots (Function.update rv 0 (a.get i)) w:=by
    refine ⟨?_,zw⟩
    intro k hk
    have hd : Disjoint (RationalDataflow.ids StoredInteger.slots) work:=by decide
    exact word_of_eq (fw.tapes k (fun hm=>Finset.disjoint_left.mp hd hk hm)) (ru.1 k hk)
  have iw:=word_of_eq (fw.tapes 728 (by decide)) iu
  have ow:=word_of_eq (fw.tapes 727 (by decide))
    (word_of_eq (f0.tapes 727 (by decide) (by decide)) one)
  obtain ⟨c2,t,e2,h2,it,ot,zt,f2⟩:=StoredInteger.advance_executes i.val B indexWidth input tape w iw ow zw
  have arrayT:=StoredInteger.table_advance_frame aw f2 zt
  have geometryT : GeometryOutput.Context data base slotWidth G clock constants
      (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets false) gv) t:=by
    apply gw.storage_frame f2.memory _ (f2.tapes 962 (by decide)) arrayT.scratch arrayT.seven
    intro k hk
    exact f2.tapes k (fun hm=>Finset.disjoint_left.mp (by decide :
      Disjoint GeometryOutput.ids (NatAssign.changed 728)) hk hm)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold stepCost;omega,
    f2.output.trans (out1.trans (congrArg ((bits (loaded data gv v (a.get i))).reverse++·) f0.output)),
    geometryT,arrayT,StoredInteger.ready_advance_frame rw f2 zt,wu,it,ot,?_,reset_width _ B vu,?_,?_⟩
  · intro k hk
    exact word_of_eq (f2.tapes k (fun hm=>Finset.disjoint_left.mp
      (by decide : Disjoint ids (NatAssign.changed 728)) hk hm)) (bw k hk)
  · intro k hk
    by_cases small : k<4
    · exact zt k small
    · apply blank_of_eq (f2.tapes k ?_) (clean k hk)
      simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hk
      simp only [NatAssign.changed,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega
  · refine ⟨f2.memory.trans (fw.memory.trans f0.memory),f2.inputHead.trans (fw.inputHead.trans f0.inputHead),
      f2.randomCursor.trans (fw.randomCursor.trans f0.randomCursor),?_⟩
    intro k hk
    have ge : 10≤k:=by
      by_contra hn
      exact hk (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_range.mpr (by omega)))))
    exact (f2.tapes k (fun hm=>hk ((by decide : NatAssign.changed 728⊆stepWork) hm))).trans
      ((fw.tapes k (fun hm=>hk (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))).trans
        (f0.tapes k ge (fun hm=>hk (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hm))))))

#print axioms step_executes
end Maxwell.Continuum.DecoderRow
