import Maxwell.Continuum.StoredIntegerCursor

/-! One fixed serializer iteration reads, emits and advances the stored
index. It preserves the runtime countdown word. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def stepCode : Code := .seq code advanceCode

theorem step_executes {n : ℕ} (a : Table n) (z : ℕ→ℤ)
    (hc : ∀i:Fin n,a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (i : Fin n) (hi : i.val.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hindex : RationalAccumulator.Word s.val 728 i.val)
    (hone : RationalAccumulator.Word s.val 727 1) :
    ∃cost t,Executes input tape stepCode cost s t ∧ cost≤2^23*(B+5)^2 ∧
      Ready slots (Function.update v 0 (a.get i)) t ∧ a.Ready t ∧
      WidthBank slots B (Function.update v 0 (a.get i)) ∧
      t.val.output=(Codec.int (z i.val)).reverse++s.val.output ∧
      RationalAccumulator.Word t.val 728 (i.val+1) ∧ RationalAccumulator.Word t.val 727 1 ∧
      t.val.memory=s.val.memory ∧
      (∀k,10 ≤ k → k∉cellPorts 0 → k≠728 → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,s0,e0,hc0,r0,a0,w0,out0,mem0,keep0⟩ := executes a z hc B hm i hi v hv
    input tape s hr ha hindex
  have index0 := RationalAccumulator.word_of_eq (keep0 728 (by decide) (by decide)) hindex
  have one0 := RationalAccumulator.word_of_eq (keep0 727 (by decide) (by decide)) hone
  obtain ⟨c1,t,e1,hc1,index1,one1,zero1,frame1⟩ := advance_executes i.val B hi input tape s0 index0 one0 r0.2
  refine ⟨c0+c1,t,e0.seq e1,?_,ready_advance_frame r0 frame1 zero1,
    table_advance_frame a0 frame1 zero1,w0,frame1.output.trans out0,index1,one1,
    frame1.memory.trans mem0,?_⟩
  · nlinarith only [hc0,hc1,Nat.zero_le B]
  · intro k hk hcell hindex
    exact (frame1.tapes k (by simp only [NatAssign.changed,Finset.mem_insert,Finset.mem_singleton];omega)).trans
      (keep0 k hk hcell)

#print axioms step_executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
