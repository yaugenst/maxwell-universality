import Maxwell.Continuum.SourceRoutingScatterStep
import Maxwell.Continuum.SourceRoutingScatterData

/-! State invariant for the actual incidence traversal. Array dimensions,
address arithmetic, and disjointness are static semantic data; all endpoint
and rank payloads are read from the represented source arrays. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Plan (k n : ℕ) where
  routing : Layout n
  inputLayout : IncidenceEncoding.Layout
  clock : List Bool
  half : ℕ
  half_pos : 0<half
  endpoint : Vector ℕ k
  rank : Vector ℕ k
  source : Fin k→Fin n
  target : Fin k→Fin n
  source_eq : ∀i,(source i).val=PortIndices.sourceIndex half (endpoint.get i) (rank.get i)
  target_eq : ∀i,(target i).val=PortIndices.targetIndex half i.val
  width_pos : 0 < inputLayout.endpointWidth
  endpoint_fits : ∀i,endpoint.get i<2^inputLayout.endpointWidth
  rank_fits : ∀i,rank.get i<4
  endpoint_forward : IncidenceEncoding.Separated inputLayout.baseEndpoint (k*inputLayout.endpointWidth)
    routing.forward (n*n.bits.length)
  endpoint_backward : IncidenceEncoding.Separated inputLayout.baseEndpoint (k*inputLayout.endpointWidth)
    routing.backward (n*n.bits.length)
  rank_forward : IncidenceEncoding.Separated inputLayout.baseRank (k*2) routing.forward (n*n.bits.length)
  rank_backward : IncidenceEncoding.Separated inputLayout.baseRank (k*2) routing.backward (n*n.bits.length)

def boundWidth {k n : ℕ} (p : Plan k n) : ℕ :=
  p.half.bits.length+k.bits.length+p.inputLayout.endpointWidth+
    p.inputLayout.baseEndpoint.bits.length+p.inputLayout.baseRank.bits.length+3
def stepCost {k n : ℕ} (p : Plan k n) : ℕ :=
  2^140*(boundWidth p+2)^2+operationCap p.routing

structure Runtime {k n : ℕ} (p : Plan k n) (done : ℕ) (s : Store) : Prop where
  done_le : done≤k
  ready : Ready s.val
  metadata : Metadata p.routing s.val
  descriptor : Descriptor p.inputLayout p.clock s.val
  endpoints : BitArray.Represents s.val.memory p.inputLayout.baseEndpoint p.inputLayout.endpointWidth
    (IncidenceEncoding.words p.inputLayout.endpointWidth p.endpoint)
  ranks : BitArray.Represents s.val.memory p.inputLayout.baseRank 2 (IncidenceEncoding.words 2 p.rank)
  stored : Stored p.routing (forward p.source p.target done) (backward p.source p.target done) s.val
  bank : NatAssign.Bank PortArithmetic.ids (seed p.half done 0 0) s.val
  scratch : Blank s.val 753

theorem incidence_width {k n : ℕ} (p : Plan k n) (i : Fin k) :
    i.val.bits.length≤boundWidth p := by
  have h := Nat.size_le_size i.isLt.le
  rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at h
  unfold boundWidth
  omega

theorem runtime_step {k n : ℕ} (p : Plan k n) (i : Fin k)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Runtime p i.val s) :
    ∃steps t, Executes input tape stepCode steps s t ∧ steps≤stepCost p ∧
      Runtime p (i.val+1) t ∧ RoutingOutside p.routing s.val t.val ∧ ArchiveFrame work s.val t.val := by
  have hB : 2≤boundWidth p := by unfold boundWidth; omega
  have hwidth : p.inputLayout.endpointWidth≤boundWidth p := by unfold boundWidth; omega
  have hhalf : p.half.bits.length≤boundWidth p := by unfold boundWidth; omega
  have heb : p.inputLayout.baseEndpoint.bits.length≤boundWidth p := by unfold boundWidth; omega
  have hrb : p.inputLayout.baseRank.bits.length≤boundWidth p := by unfold boundWidth; omega
  have hew : (p.endpoint.get i).bits.length≤boundWidth p := by
    have hh := Nat.size_le.mpr (p.endpoint_fits i)
    rw [←Nat.size_eq_bits_len] at hh
    exact hh.trans hwidth
  have hrw : (p.rank.get i).bits.length≤boundWidth p := by
    have hh : (p.rank.get i).size≤2 := Nat.size_le.mpr (p.rank_fits i)
    rw [←Nat.size_eq_bits_len] at hh
    exact hh.trans hB
  obtain ⟨steps,t,he,hc,rt,mt,bt,zt,st,hout,hframe⟩ := step_executes p.routing p.inputLayout p.clock
    p.endpoint p.rank p.source p.target p.half p.half_pos i (p.source_eq i) (p.target_eq i)
    p.width_pos (p.endpoint_fits i) (p.rank_fits i)
    (forward p.source p.target i.val) (backward p.source p.target i.val)
    (boundWidth p) hB hwidth (incidence_width p i) heb hrb
    (seed_width _ _ _ _ _ hhalf (incidence_width p i) hew hrw)
    input tape s hs.ready hs.metadata hs.descriptor hs.bank hs.scratch hs.endpoints hs.ranks hs.stored
  have dt := hs.descriptor.transport (fun j hj => hframe.tapes j (Or.inr (by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj; omega)) (by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide))
  refine ⟨steps,t,he,hc,⟨by omega,rt,mt,dt,
    hout.preserves _ _ _ hs.endpoints p.endpoint_forward p.endpoint_backward,
    hout.preserves _ _ _ hs.ranks p.rank_forward p.rank_backward,?_,bt,zt⟩,hout,hframe⟩
  rw [forward_step,backward_step]
  exact st

theorem Runtime.counter_frame {k n : ℕ} {p : Plan k n} {done : ℕ} {s t : Store}
    (hs : Runtime p done s) (hmem : t.val.memory=s.val.memory)
    (keep : ∀j,j≠779→t.val.tapes j=s.val.tapes j) : Runtime p done t := by
  have ready := Initialize.ready_of_keep hs.ready (fun j hj => keep j (by omega))
  have mt : Metadata p.routing t.val :=
    ⟨RationalAccumulator.word_of_eq (keep 709 (by decide)) hs.metadata.count,
      RationalAccumulator.word_of_eq (keep 711 (by decide)) hs.metadata.width,
      RationalAccumulator.word_of_eq (keep 716 (by decide)) hs.metadata.forward,
      RationalAccumulator.word_of_eq (keep 717 (by decide)) hs.metadata.backward,
      BankArray.word_of_eq (keep 718 (by decide)) hs.metadata.clock⟩
  have desc := hs.descriptor.transport (fun j hj => keep j (by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj; omega))
  refine ⟨hs.done_le,ready,mt,desc,?_,?_,?_,?_,
    RationalAccumulator.blank_of_eq (keep 753 (by decide)) hs.scratch⟩
  · rw [hmem]; exact hs.endpoints
  · rw [hmem]; exact hs.ranks
  · constructor
    · rw [hmem]; exact hs.stored.forward
    · rw [hmem]; exact hs.stored.backward
  · intro j hj
    have h779 : j≠779 := by
      simp only [PortArithmetic.ids,PortArithmetic.ports,
        Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hj
      omega
    exact RationalAccumulator.word_of_eq (keep j h779) (hs.bank j hj)

theorem Runtime.counted {k n : ℕ} {p : Plan k n} {done : ℕ} {s t : Store}
    (hs : Runtime p done s) (hf : CountedShifted.Frame 779 s t) : Runtime p done t :=
  hs.counter_frame hf.2.2.1 hf.2.2.2.2.2.1

#print axioms runtime_step
#print axioms Runtime.counted

end Maxwell.Cost.RoutingPorts.Complete.Scatter
