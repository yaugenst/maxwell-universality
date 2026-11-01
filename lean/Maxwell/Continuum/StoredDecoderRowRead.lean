import Maxwell.Continuum.StoredDecoderRowFrame

/-! A row's operands are obtained by three charged packed-coordinate reads
and one charged read of the chronological strength table. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def coordinatePorts : Finset ℕ:={976,977,978}
def coordinateValues {n : ℕ} (data : Vector ℕ n) (gv v : ℕ→ℕ) (i : ℕ):=
  if i∈coordinatePorts then GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets false) gv i else v i
def loaded {n : ℕ} (data : Vector ℕ n) (gv v : ℕ→ℕ) (x : Parts):=
  Function.update (coordinateValues data gv v) 1000 x.positive
def readCode : Code:=.seq (GeometryOutput.readPlanCode (GeometryOutput.tripleTargets false))
  (PartArray.readAtCode 728 0)
def readWork : Finset ℕ:={971,976,977,978,1000,1001,1002}

theorem read_executes {n J base slotWidth G : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base slotWidth G clock constants gv s)
    (slotPositive : 0<slotWidth) (slotBound : slotWidth≤G) (hlen : clock.length=slotWidth)
    (hn : n.bits.length≤G) (fits : ∀i,(data.get i).bits.length≤slotWidth)
    (hbase : constants 960=base) (hwidth : constants 961=slotWidth) (hone : constants 970=1)
    (range : gv 971+3≤n) (a : Table J) (table : a.Ready s)
    (rv : ℕ→Parts) (raw : RationalDataflow.Ready StoredInteger.slots rv s)
    (i : Fin J) (index : Word s.val 728 i.val)
    (v : ℕ→ℕ) (B : ℕ) (hGB : G≤B)
    (bank : NatAssign.Bank ids v s.val) (bound : ∀k∈ids,(v k).bits.length≤B)
    (rawWidth : WidthBank StoredInteger.slots B rv) (metadata : a.MetadataWidth B)
    (indexWidth : i.val.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool):
    ∃cost t,Executes input tape readCode cost s t ∧cost≤2^26*(B+5)^2 ∧
      GeometryOutput.Context data base slotWidth G clock constants
        (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets false) gv) t ∧
      a.Ready t ∧RationalDataflow.Ready StoredInteger.slots (Function.update rv 0 (a.get i)) t ∧
      WidthBank StoredInteger.slots B (Function.update rv 0 (a.get i)) ∧
      Word t.val 728 i.val ∧NatAssign.Bank ids (loaded data gv v (a.get i)) t.val ∧
      (∀k∈ids,(loaded data gv v (a.get i) k).bits.length≤B) ∧
      GeometryOutput.ReadFrame readWork s.val t.val:=by
  obtain ⟨c0,u,e0,h0,gu,f0⟩:=g.read_plan (GeometryOutput.tripleTargets false)
    (GeometryOutput.tripleTargets_valid false) (GeometryOutput.tripleTargets_fixed false)
    slotPositive slotBound hlen hn fits hbase hwidth hone range input tape
  have zero : NatAssign.Scratch u.val:=by
    intro k hk
    interval_cases k
    · exact gu.ready.scratch.1
    · exact gu.ready.scratch.2.1
    · exact gu.ready.scratch.2.2.1
    · exact gu.ready.scratch.2.2.2.1
  have tableU : a.Ready u:=by
    apply table.storage_frame f0.memory _ gu.ready.scratch gu.ready.seven
    intro k hk
    apply f0.tapes k
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk;omega
    · have hd : Disjoint ({200,202,203,204,205}:Finset ℕ)
          ((GeometryOutput.tripleTargets false).toFinset∪{971}):=by decide
      exact fun hm=>Finset.disjoint_left.mp hd hk hm
  have rawU : RationalDataflow.Ready StoredInteger.slots rv u:=by
    refine ⟨?_,zero⟩
    intro k hk
    apply word_of_eq (f0.tapes k (ids_ge_ten _ _ hk) ?_) (raw.1 k hk)
    have disjoint : Disjoint (RationalDataflow.ids StoredInteger.slots)
        ((GeometryOutput.tripleTargets false).toFinset∪{971}):=by decide
    exact fun hm=>Finset.disjoint_left.mp disjoint hk hm
  have indexU : Word u.val 728 i.val:=word_of_eq (f0.tapes 728 (by decide) (by decide)) index
  have bankU : NatAssign.Bank ids (coordinateValues data gv v) u.val:=by
    intro k hk
    by_cases point : k∈coordinatePorts
    · rw [coordinateValues,ite_eq_left point]
      exact gu.ready.bank k ((by decide : coordinatePorts⊆GeometryOutput.ids) point)
    · rw [coordinateValues,ite_eq_right point]
      apply word_of_eq (f0.tapes k ?_ ?_) (bank k hk)
      · simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk;omega
      · have notIndex : k≠971:=by
          simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk;omega
        simpa [GeometryOutput.tripleTargets,coordinatePorts,notIndex] using point
  have boundU : ∀k∈ids,(coordinateValues data gv v k).bits.length≤B:=by
    intro k hk
    by_cases point : k∈coordinatePorts
    · rw [coordinateValues,ite_eq_left point]
      exact (gu.wordWidth k ((by decide : coordinatePorts⊆GeometryOutput.ids) point)).trans hGB
    · simpa only [coordinateValues,ite_eq_right point] using bound k hk
  obtain ⟨c1,t,e1,h1,rt,arrayT,it,f1⟩:=PartArray.readAt_executes a StoredInteger.slots 728 0
    (by decide) (by decide) (by decide) rv input tape i.val.bits i (addressValue_bits _)
    u rawU tableU indexU
  have gt : GeometryOutput.Context data base slotWidth G clock constants
      (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets false) gv) t:=by
    apply gu.storage_frame f1.memory _ (f1.tapes 962 (by decide) (by decide)) arrayT.scratch arrayT.seven
    intro k hk
    apply f1.tapes k
    · exact (by omega : 10≤960).trans (GeometryOutput.ids_ge k hk)
    · simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk
      simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,
        Finset.mem_singleton,not_or]
      omega
  have valueWidth:=a.get_width B metadata u tableU i
  have rawFinal:=rawWidth.update 0 valueWidth
  have bankT : NatAssign.Bank ids (loaded data gv v (a.get i)) t.val:=by
    intro k hk
    by_cases h1000 : k=1000
    · subst k
      have hh:=rt.1 (positivePort 0) (cell_mem (by decide : 0∈StoredInteger.slots) (by simp [cellPorts]))
      have hp : Word t.val (positivePort 0) (a.get i).positive:=by
        simpa only [dataValues_positive,Function.update_self] using hh
      change Word t.val 1000 (a.get i).positive at hp
      simpa only [loaded,Function.update_self] using hp
    · rw [loaded,Function.update_of_ne h1000]
      apply word_of_eq (f1.tapes k ?_ ?_) (bankU k hk)
      · simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk;omega
      · simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk
        simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,
          Finset.mem_singleton,not_or]
        omega
  refine ⟨c0+c1,t,e0.seq e1,?_,gt,arrayT,rt,rawFinal,it,bankT,?_,?_⟩
  · have hc:=a.readCost_bound B metadata i.val.bits indexWidth (rv 0) (rawWidth 0 (by decide))
    rw [GeometryOutput.tripleTargets_length] at h0
    have hg:=Nat.pow_le_pow_left (show G+3≤B+5 by omega) 2
    nlinarith only [h0,h1,hc,hg,Nat.zero_le B]
  · intro k hk
    by_cases h1000 : k=1000
    · subst k;simpa only [loaded,Function.update_self] using valueWidth.1
    · simpa only [loaded,Function.update_of_ne h1000] using boundU k hk
  · refine ⟨f1.memory.trans f0.memory,f1.inputHead.trans f0.inputHead,
      f1.randomCursor.trans f0.randomCursor,f1.output.trans f0.output,?_⟩
    intro k hk hnot
    have hpoint : k∉(GeometryOutput.tripleTargets false).toFinset∪{971}:=by
      exact fun hm=>hnot ((by decide : (GeometryOutput.tripleTargets false).toFinset∪{971}⊆readWork) hm)
    have hcell : k∉cellPorts 0:=by
      exact fun hm=>hnot ((by decide : cellPorts 0⊆readWork) hm)
    exact (f1.tapes k hk hcell).trans (f0.tapes k hk hpoint)

#print axioms read_executes
end Maxwell.Continuum.DecoderRow
