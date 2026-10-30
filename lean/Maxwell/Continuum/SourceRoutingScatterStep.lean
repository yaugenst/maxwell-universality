import Maxwell.Continuum.SourceRoutingScatterBank
import Maxwell.Continuum.SourceRoutingInitializeBoth
import Maxwell.Continuum.SourceRoutingOperations

/-! One fixed scatter iteration reads the actual endpoint and saved rank,
computes both addresses, writes the pair, clears its temporaries, and advances
the canonical incidence cursor. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000

def work : Finset ℕ := {37}∪PortArithmetic.privateWork
def stepCode : Code := .seq readCode (.seq PortArithmetic.privateCode
  (.seq pairCode (.seq (NatAssign.code cleanup) (PhysicalEmit.incrementCode 733))))

theorem work_metadata (i : ℕ) (hi : i∈work) :
    i≠709 ∧ i≠711 ∧ i≠716 ∧ i≠717 ∧ i≠718 := by
  simp only [work,PortArithmetic.privateWork,PortArithmetic.ids,PortArithmetic.ports,
    Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem step_executes {k n : ℕ} (l : Layout n) (el : IncidenceEncoding.Layout) (clock : List Bool)
    (endpoint rank : Vector ℕ k) (source target : Fin k→Fin n) (half : ℕ) (hh : 0<half)
    (i : Fin k) (hsource : (source i).val=PortIndices.sourceIndex half (endpoint.get i) (rank.get i))
    (htarget : (target i).val=PortIndices.targetIndex half i.val)
    (hw : 0<el.endpointWidth) (hefit : endpoint.get i<2^el.endpointWidth) (hrfit : rank.get i<4)
    (forward backward : Vector ℕ n) (B : ℕ) (hB : 2≤B)
    (hwidth : el.endpointWidth≤B) (hic : i.val.bits.length≤B)
    (heb : el.baseEndpoint.bits.length≤B) (hrb : el.baseRank.bits.length≤B)
    (hbankWidth : ∀j∈PortArithmetic.ids,(seed half i.val (endpoint.get i) (rank.get i) j).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hm : Metadata l s.val) (hd : Descriptor el clock s.val)
    (hbank : NatAssign.Bank PortArithmetic.ids (seed half i.val 0 0) s.val) (h753 : Blank s.val 753)
    (he : BitArray.Represents s.val.memory el.baseEndpoint el.endpointWidth (IncidenceEncoding.words el.endpointWidth endpoint))
    (hr : BitArray.Represents s.val.memory el.baseRank 2 (IncidenceEncoding.words 2 rank))
    (ha : Stored l forward backward s.val) :
    ∃steps t, Executes input tape stepCode steps s t ∧
      steps≤2^140*(B+2)^2+operationCap l ∧ Ready t.val ∧ Metadata l t.val ∧
      NatAssign.Bank PortArithmetic.ids (seed half (i.val+1) 0 0) t.val ∧ Blank t.val 753 ∧
      Stored l (forward.set (source i) (target i).val) (backward.set (target i) (source i).val) t.val ∧
      RoutingOutside l s.val t.val ∧ ArchiveFrame work s.val t.val := by
  have s734 : Blank s.val 734 := (RationalAccumulator.zero_word_iff_blank _ _).mp (hbank 734 (by decide))
  have s735 : Blank s.val 735 := (RationalAccumulator.zero_word_iff_blank _ _).mp (hbank 735 (by decide))
  obtain ⟨ca,a,ea,hca,a734,a735,ra,ma,fa⟩ := read_inputs el clock endpoint rank i hw hefit hrfit
    input tape s hs hd (hbank 733 (by decide)) s734 s735 he hr
  have ba := read_bank half endpoint rank i hbank a734 a735 fa
  have a753 := RationalAccumulator.blank_of_eq (fa.tapes 753 (by decide) (by decide)) h753
  obtain ⟨cb,b,eb,hcb,bb,rb,b753,fb⟩ := PortArithmetic.private_executes
    (seed half i.val (endpoint.get i) (rank.get i)) (seed_zero _ _ _ _)
    hh B hB hbankWidth input tape a ba ra a753
  have bframe : ArchiveFrame work s.val b.val :=
    (fa.mono (by decide)).trans ((ArchiveFrame.of_binary fb).mono (by decide))
  have bm := hm.archive bframe work_metadata
  have bs : Stored l forward backward b.val := by
    constructor
    · rw [fb.memory,ma]; exact ha.forward
    · rw [fb.memory,ma]; exact ha.backward
  have b730 : Word b.val 730 (source i).val := by
    have hb := bb 730 (by decide)
    rw [PortArithmetic.source_value] at hb
    change Word b.val 730 (PortIndices.sourceIndex half (endpoint.get i) (rank.get i)) at hb
    rw [←hsource] at hb
    exact hb
  have b731 : Word b.val 731 (target i).val := by
    have hb := bb 731 (by decide)
    rw [PortArithmetic.target_value] at hb
    change Word b.val 731 (PortIndices.targetIndex half i.val) at hb
    rw [←htarget] at hb
    exact hb
  obtain ⟨cc,c,ec,hcc,rc,cm,cs,mc,fc⟩ := pair_write l forward backward (source i) (target i)
    input tape b rb bm bs b730 b731
  have bc : NatAssign.Bank PortArithmetic.ids
      (PortArithmetic.output (seed half i.val (endpoint.get i) (rank.get i))) c.val := by
    intro j hj
    exact RationalAccumulator.word_of_eq (fc.tapes j (Or.inr (PortArithmetic.ids_lower j hj)) (by
      simp only [PortArithmetic.ids,PortArithmetic.ports,
        Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hj
      simp only [Finset.mem_singleton]
      omega)) (bb j hj)
  obtain ⟨cd,d,ed,hcd,bd,rd,fd⟩ := cleanup_executes half i.val (endpoint.get i) (rank.get i) B hB
    hbankWidth input tape c bc rc
  have d753 := RationalAccumulator.blank_of_eq (fd.tapes 753 (by decide))
    (RationalAccumulator.blank_of_eq (fc.tapes 753 (by decide) (by decide)) b753)
  obtain ⟨ce,t,hce,ee,t733,fe⟩ := PhysicalEmit.increment 733 i.val input tape d (bd 733 (by decide))
  have rt := Initialize.ready_of_keep rd (fun j hj => fe.tapes j (by simp; omega))
  have bt : NatAssign.Bank PortArithmetic.ids (seed half (i.val+1) 0 0) t.val := by
    intro j hj
    by_cases h733 : j=733
    · subst j
      exact t733
    · have h := RationalAccumulator.word_of_eq (fe.tapes j (by simpa using h733)) (bd j hj)
      simpa only [seed,h733,ite_false] using h
  have ef : ArchiveFrame {733} d.val t.val :=
    ⟨fe.inputHead,fe.randomCursor,fe.output,fun j _ hj => fe.tapes j hj⟩
  have frame : ArchiveFrame work s.val t.val := bframe.trans
    ((ArchiveFrame.of_complete fc).mono (by decide) |>.trans
      (((ArchiveFrame.of_binary fd).mono (by decide)).trans (ef.mono (by decide))))
  have mt := hm.archive frame work_metadata
  have st : Stored l (forward.set (source i) (target i).val) (backward.set (target i) (source i).val) t.val := by
    constructor
    · rw [fe.memory,fd.memory]; exact cs.forward
    · rw [fe.memory,fd.memory]; exact cs.backward
  have outa : RoutingOutside l s.val a.val := RoutingOutside.of_memory ma
  have outb : RoutingOutside l a.val b.val := RoutingOutside.of_memory fb.memory
  have outc : RoutingOutside l b.val c.val := RoutingOutside.of_pair_write l (source i) (target i) mc
  have outd : RoutingOutside l c.val d.val := RoutingOutside.of_memory fd.memory
  have oute : RoutingOutside l d.val t.val := RoutingOutside.of_memory fe.memory
  refine ⟨ca+(cb+(cc+(cd+ce))),t,ea.seq (eb.seq (ec.seq (ed.seq ee))),?_,rt,mt,bt,
    RationalAccumulator.blank_of_eq (fe.tapes 753 (by decide)) d753,st,
    outa.trans (outb.trans (outc.trans (outd.trans oute))),frame⟩
  have hca' := hca.trans (readCost_bound el clock i.val B hB hwidth hd.clock_length hic heb hrb)
  have hcc' := hcc.trans (pairCost_bound l (source i) (target i))
  have hinc : 12*i.val.bits.length+18≤100*(B+2)^2 := by nlinarith
  nlinarith only [hca',hcb,hcc',hcd,hce,hinc,Nat.one_le_pow 2 (B+2) (by omega)]

#print axioms step_executes

end Maxwell.Cost.RoutingPorts.Complete.Scatter
