import Maxwell.Continuum.StoredDyadicEmission
import Maxwell.Continuum.StoredSerializationTransfer
import Maxwell.Continuum.RationalDataflowProgramFootprint

/-! Actual indexed access and numerator emission for a table of raw dyadic
values. The stronger canonical-integer table invariant is not required. -/
namespace Maxwell.Continuum.RationalDataflow.StoredDyadic
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
open StoredInteger (slots)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def readCode : Code := .seq (readAtCode 728 0) code
def registerWidth (P B : ℕ) : ℕ := 2*B+P+3

theorem read_executes {n P : ℕ} (a : Table n) (d : Fin n→Dyadic P)
    (hc : ∀i,(a.get i).Valid ∧ (a.get i).value=(d i).value)
    (B : ℕ) (hm : a.MetadataWidth B) (i : Fin n) (hi : i.val.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots (registerWidth P B) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s) (hindex : Word s.val 728 i.val)
    (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t values,Executes input tape readCode cost s t ∧ cost≤2^148*(P+B+6)^2 ∧
      Ready slots values t ∧ WidthBank slots (registerWidth P B) values ∧ a.Ready t ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      t.val.output=(Codec.int (d i).numerator).reverse++s.val.output ∧
      t.val.memory=s.val.memory ∧
      (∀k,10≤k → k∉DyadicFloor.StoredPower.workspace slots → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,s0,e0,hc0,r0,a0,_,f0⟩ := readAt_executes a slots 728 0 (by decide) (by decide)
    (by decide) v input tape i.val.bits i (addressValue_bits _) s hr ha hindex
  have w0 : WidthBank slots B (Function.update v 0 (a.get i)) := by
    intro j hj
    have he : j=0 := by simpa only [slots,Finset.mem_singleton] using hj
    subst j
    exact a.get_width B hm s ha i
  have clean0 : DyadicFloor.Clean s0.val := by
    refine ⟨RationalAccumulator.blank_of_eq
      (e0.protectsTape 4 (by decide : (readAtCode 728 0).protectsTape 4=true)) hclean.1,?_⟩
    intro k hk
    have hg : 10≤k ∧ k<1000 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    have ho : k∉cellPorts 0 := by
      simp only [cellPorts,positivePort,negativePort,denominatorPort,
        Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.blank_of_eq (f0.tapes k hg.1 ho) (hclean.2 k hk)
  have power0 := RationalAccumulator.word_of_eq (f0.tapes 144 (by decide) (by decide)) hpower
  obtain ⟨c1,t,e1,hc1,r1,w1,z1,p1,out1,mem1,keep1⟩ := executes (d i)
    (Function.update v 0 (a.get i)) B w0 (hc i).1 (hc i).2 input tape s0 r0 clean0 power0
  have table1 : a.Ready t := a0.memory_frame mem1 (fun k hk=>keep1 k (by
    have hd : Disjoint tablePorts (DyadicFloor.StoredPower.workspace slots) := by decide
    exact fun hh=>Finset.disjoint_left.mp hd hk hh)) r1.2
  have hBC : B≤registerWidth P B := by unfold registerWidth;omega
  have costread := a.readCost_bound (registerWidth P B) (hm.mono hBC) i.val.bits (hi.trans hBC)
    (v 0) (hv 0 (by decide))
  refine ⟨c0+c1,t,outputValues (d i) (Function.update v 0 (a.get i)),e0.seq e1,?_,
    r1,w1,table1,z1,p1,by simpa only [f0.output] using out1,mem1.trans f0.memory,?_⟩
  · unfold registerWidth at costread
    nlinarith only [hc0,costread,hc1,Nat.zero_le P,Nat.zero_le B]
  · intro k hk ho
    have hcell : k∉cellPorts 0 := by
      intro hc'
      apply ho
      have hid := cell_mem (by decide : 0∈slots) hc'
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hid)))
    exact (keep1 k ho).trans (f0.tapes k hk hcell)

#print axioms read_executes
end Maxwell.Continuum.RationalDataflow.StoredDyadic
