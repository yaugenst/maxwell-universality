import Maxwell.Continuum.StoredDyadicRead
import Maxwell.Continuum.StoredIntegerCursor

/-! One fixed dyadic-array serializer iteration, including cursor advance. -/
namespace Maxwell.Continuum.RationalDataflow.StoredDyadic
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
open StoredInteger (slots)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def stepCode : Code := .seq readCode StoredInteger.advanceCode

theorem step_executes {n P : ℕ} (a : Table n) (d : ℕ→Dyadic P)
    (hc : ∀i:Fin n,(a.get i).Valid ∧ (a.get i).value=(d i.val).value)
    (B : ℕ) (hm : a.MetadataWidth B) (i : Fin n) (hi : i.val.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots (registerWidth P B) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s) (hindex : Word s.val 728 i.val)
    (hone : Word s.val 727 1) (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t values,Executes input tape stepCode cost s t ∧ cost≤2^149*(P+B+6)^2 ∧
      Ready slots values t ∧ WidthBank slots (registerWidth P B) values ∧ a.Ready t ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      t.val.output=(Codec.int (d i.val).numerator).reverse++s.val.output ∧
      Word t.val 728 (i.val+1) ∧ Word t.val 727 1 ∧ t.val.memory=s.val.memory ∧
      (∀k,10≤k → k∉DyadicFloor.StoredPower.workspace slots → k≠728 → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,s0,values,e0,hc0,r0,w0,a0,z0,p0,out0,mem0,keep0⟩ :=
    read_executes a (fun j=>d j.val) hc B hm i hi v hv input tape s hr ha hindex hclean hpower
  have index0 := RationalAccumulator.word_of_eq (keep0 728 (by decide) (by decide)) hindex
  have one0 := RationalAccumulator.word_of_eq (keep0 727 (by decide) (by decide)) hone
  obtain ⟨c1,t,e1,hc1,index1,one1,scratch,frame⟩ :=
    StoredInteger.advance_executes i.val B hi input tape s0 index0 one0 r0.2
  have outside (k : ℕ) (hk : k≠0 ∧ k≠1 ∧ k≠2 ∧ k≠3 ∧ k≠728) :
      k∉NatAssign.changed 728 := by
    simp only [NatAssign.changed,Finset.mem_insert,Finset.mem_singleton]
    tauto
  refine ⟨c0+c1,t,values,e0.seq e1,?_,StoredInteger.ready_advance_frame r0 frame scratch,
    w0,StoredInteger.table_advance_frame a0 frame scratch,?_,
    RationalAccumulator.word_of_eq (frame.tapes 144 (by decide)) p0,
    frame.output.trans out0,index1,one1,frame.memory.trans mem0,?_⟩
  · nlinarith only [hc0,hc1,Nat.zero_le P,Nat.zero_le B]
  · refine ⟨RationalAccumulator.blank_of_eq (frame.tapes 4 (by decide)) z0.1,?_⟩
    intro k hk
    have ho : k≠0 ∧ k≠1 ∧ k≠2 ∧ k≠3 ∧ k≠728 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact RationalAccumulator.blank_of_eq (frame.tapes k (outside k ho)) (z0.2 k hk)
  · intro k hk ho hindex'
    exact (frame.tapes k (outside k (by omega))).trans (keep0 k hk ho)

#print axioms step_executes
end Maxwell.Continuum.RationalDataflow.StoredDyadic
