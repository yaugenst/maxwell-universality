import Maxwell.Continuum.SourceRoutingOperations
import Maxwell.Continuum.SourceRoutingCursorData
import Maxwell.Continuum.SourceRoutingMemory

/-! Actual stored states and charged primitives of the routing completion
pass. Both cursors and every tested sentinel are runtime data. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def cursorWork : Finset ℕ := {37,730,731,752}

structure CursorFrame {n : ℕ} (l : Layout n) (s t : BitRAMState) : Prop where
  control : Frame cursorWork s t
  outside : RoutingOutside l s t

theorem CursorFrame.trans {n : ℕ} {l : Layout n} {s t u : BitRAMState}
    (h : CursorFrame l s t) (k : CursorFrame l t u) : CursorFrame l s u :=
  ⟨h.control.trans k.control,h.outside.trans k.outside⟩

theorem cursorWork_metadata (i : ℕ) (hi : i∈cursorWork) : 730 ≤ i ∨ i=37 := by
  simp only [cursorWork,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem linear_cost_bound {n : ℕ} (l : Layout n) :
    200*n.bits.length+200≤operationCap l := by
  have h : n.bits.length+6≤scale l := by unfold scale; omega
  unfold operationCap
  nlinarith only [h, sq_nonneg ((scale l : ℤ)-1)]

theorem Stored.of_memory_eq {n : ℕ} {l : Layout n} {a b : Vector ℕ n}
    {s t : BitRAMState} (h : Stored l a b s) (hm : t.memory=s.memory) : Stored l a b t := by
  constructor
  · rw [hm]
    exact h.forward
  · rw [hm]
    exact h.backward

structure CursorRuntime {n : ℕ} (l : Layout n) (p : CompletionPlan n)
    (d i j : ℕ) (s : Store) : Prop where
  ready : Ready s.val
  metadata : Metadata l s.val
  stored : Stored l (p.forward d) (p.backward d) s.val
  leftWord : RationalAccumulator.Word s.val 730 i
  rightWord : RationalAccumulator.Word s.val 731 j

namespace CursorRuntime

theorem preserve {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    {s t : Store} (h : CursorRuntime l p d i j s) (hr : Ready t.val)
    (hm : t.val.memory=s.val.memory) {work : Finset ℕ}
    (hf : Frame work s.val t.val) (hw : work⊆cursorWork)
    (hl : 730∉work) (hj : 731∉work) : CursorRuntime l p d i j t := by
  refine ⟨hr,h.metadata.frame hf (fun k hk => cursorWork_metadata k (hw hk)),?_,
    RationalAccumulator.word_of_eq (hf.tapes 730 (by decide) hl) h.leftWord,
    RationalAccumulator.word_of_eq (hf.tapes 731 (by decide) hj) h.rightWord⟩
  exact h.stored.of_memory_eq hm

theorem test {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hi : i≤n) :
    ∃cost t, Executes input tape (cursorTestCode 730) cost s t ∧ cost≤operationCap l ∧
      CursorRuntime l p d i j t ∧ (t.val.registers 2=true ↔ i<n) ∧
      CursorFrame l s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hr,hm,hf⟩ := cursor_test l 730 i (by decide) hi
    input tape s h.ready h.metadata h.leftWord
  exact ⟨cost,t,he,hc.trans (linear_cost_bound l),
    h.preserve hr hm hf (by decide) (by decide) (by decide),hb,
    ⟨hf.mono (by decide),RoutingOutside.of_memory hm⟩⟩

theorem probe_left {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hi : i<n) :
    ∃cost t, Executes input tape (probeCode 730 716) cost s t ∧ cost≤operationCap l ∧
      CursorRuntime l p d i j t ∧
      (t.val.registers 2=true ↔ (p.forward d).get ⟨i,hi⟩<n) ∧
      CursorFrame l s.val t.val := by
  obtain ⟨cost,t,hc,he,hb,hr,hm,hf⟩ := probe 730 716 (by decide) (by decide)
    (p.forward d) ⟨i,hi⟩ l.forward l.clock l.positive l.clock_length input tape s h.ready
    h.metadata.count h.metadata.width h.leftWord h.metadata.forward h.metadata.clock
    h.stored.forward (p.forward_le d ⟨i,hi⟩)
  refine ⟨cost,t,he,?_,h.preserve hr hm hf (by decide) (by decide) (by decide),hb,
    ⟨hf.mono (by decide),RoutingOutside.of_memory hm⟩⟩
  exact (hc.trans (probeCost_bound l ⟨i,hi⟩ l.forward (by omega))).trans (Nat.div_le_self ..)

theorem probe_right {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hj : j<n) :
    ∃cost t, Executes input tape (probeCode 731 717) cost s t ∧ cost≤operationCap l ∧
      CursorRuntime l p d i j t ∧
      (t.val.registers 2=true ↔ (p.backward d).get ⟨j,hj⟩<n) ∧
      CursorFrame l s.val t.val := by
  obtain ⟨cost,t,hc,he,hb,hr,hm,hf⟩ := probe 731 717 (by decide) (by decide)
    (p.backward d) ⟨j,hj⟩ l.backward l.clock l.positive l.clock_length input tape s h.ready
    h.metadata.count h.metadata.width h.rightWord h.metadata.backward h.metadata.clock
    h.stored.backward (p.backward_le d ⟨j,hj⟩)
  refine ⟨cost,t,he,?_,h.preserve hr hm hf (by decide) (by decide) (by decide),hb,
    ⟨hf.mono (by decide),RoutingOutside.of_memory hm⟩⟩
  exact (hc.trans (probeCost_bound l ⟨j,hj⟩ l.backward (by omega))).trans (Nat.div_le_self ..)

theorem increment_left {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hi : i≤n) :
    ∃cost t, Executes input tape (PhysicalEmit.incrementCode 730) cost s t ∧
      cost≤operationCap l ∧ CursorRuntime l p d (i+1) j t ∧ CursorFrame l s.val t.val := by
  obtain ⟨cost,t,he,hc,hr,hw,hm,hf⟩ := increment_cursor 730 i (by decide) input tape s h.ready h.leftWord
  have hbits : i.bits.length≤n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hi
  refine ⟨cost,t,he,?_,⟨hr,h.metadata.frame hf (by simp),?_,hw,
    RationalAccumulator.word_of_eq (hf.tapes 731 (by decide) (by decide)) h.rightWord⟩,
    ⟨hf.mono (by decide),RoutingOutside.of_memory hm⟩⟩
  · exact (hc.trans (by omega)).trans (linear_cost_bound l)
  · exact h.stored.of_memory_eq hm

theorem increment_right {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hj : j≤n) :
    ∃cost t, Executes input tape (PhysicalEmit.incrementCode 731) cost s t ∧
      cost≤operationCap l ∧ CursorRuntime l p d i (j+1) t ∧ CursorFrame l s.val t.val := by
  obtain ⟨cost,t,he,hc,hr,hw,hm,hf⟩ := increment_cursor 731 j (by decide) input tape s h.ready h.rightWord
  have hbits : j.bits.length≤n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hj
  refine ⟨cost,t,he,?_,⟨hr,h.metadata.frame hf (by simp),?_,
    RationalAccumulator.word_of_eq (hf.tapes 730 (by decide) (by decide)) h.leftWord,hw⟩,
    ⟨hf.mono (by decide),RoutingOutside.of_memory hm⟩⟩
  · exact (hc.trans (by omega)).trans (linear_cost_bound l)
  · exact h.stored.of_memory_eq hm

theorem write_pair {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hi : i<n) (hj : j<n)
    (hd : d<p.remainingPairs.length) (hp : p.remainingPairs[d]=(⟨i,hi⟩,⟨j,hj⟩)) :
    ∃cost t, Executes input tape pairCode cost s t ∧ cost≤operationCap l ∧
      CursorRuntime l p (d+1) i j t ∧ CursorFrame l s.val t.val := by
  obtain ⟨cost,t,he,hc,hr,hm,ha,hwrite,hf⟩ := pair_write l (p.forward d) (p.backward d)
    ⟨i,hi⟩ ⟨j,hj⟩ input tape s h.ready h.metadata h.stored h.leftWord h.rightWord
  obtain ⟨hforward,hbackward⟩ := p.write_next d hd ⟨i,hi⟩ ⟨j,hj⟩ hp
  refine ⟨cost,t,he,hc.trans (pairCost_bound l _ _),⟨hr,hm,?_,
    RationalAccumulator.word_of_eq (hf.tapes 730 (by decide) (by decide)) h.leftWord,
    RationalAccumulator.word_of_eq (hf.tapes 731 (by decide) (by decide)) h.rightWord⟩,
    ⟨hf.mono (by decide),RoutingOutside.of_pair_write l _ _ hwrite⟩⟩
  simpa only [hforward,hbackward] using ha

end CursorRuntime

#print axioms CursorRuntime.probe_left
#print axioms CursorRuntime.increment_right
#print axioms CursorRuntime.write_pair

end Maxwell.Cost.RoutingPorts.Complete
