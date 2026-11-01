import Maxwell.Continuum.WellSourceReadPair
import Maxwell.Continuum.WellTargetWrite

/-! The original-well strength step reads both saved source arrays,
calculates the physical target, rounds its reciprocal, and stores all
channels. Its only numerical inputs are the actual represented words. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalWrite
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellSourceRead
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code : Code := .seq pairCode (WellTarget.writeCode .original)

def target (v : ℕ→Parts) (diagonal degree : ℕ) : ℚ :=
  (v 4).value*(((diagonal:ℚ)-8)/2-(degree:ℚ))

def output (P : ℕ) (v : ℕ→Parts) (diagonal degree : ℕ) : ℕ→Parts :=
  WellTarget.output .original P (pairValues v diagonal degree)

theorem read_target (v : ℕ→Parts) (diagonal degree : ℕ)
    (h8n : (v 8).negative=0) (h8d : (v 8).denominator=1)
    (h9n : (v 9).negative=0) (h9d : (v 9).denominator=1) :
    WellTarget.target .original (pairValues v diagonal degree)=target v diagonal degree := by
  simp only [WellTarget.target,target,pairValues_preserves v diagonal degree 4 (by decide) (by decide),
    pairValues_diagonal v diagonal degree h8n h8d,pairValues_degree v diagonal degree h9n h9d]

theorem read_clean {s t : BitRAMState} (h : DyadicFloor.Clean s) (f : WellSourceRead.Frame s t) :
    DyadicFloor.Clean t := by
  refine ⟨blank_of_eq f.four h.1,?_⟩
  intro j hj
  have bounds : 10 ≤ j ∧ j<1000 ∧ j ≠ 995 ∧ j ≠ 996 := by
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  exact blank_of_eq (f.metadata j bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2) (h.2 j hj)

theorem executes {n m : ℕ} (a : PartArray.Table m) (diagonals degrees : Vector (List Bool) n)
    (diagonalBase degreeBase P B M : ℕ) (hB : 4 ≤ B) (hP : (2^P).bits.length ≤ B)
    (hdB : diagonalBase.bits.length ≤ B) (hgB : degreeBase.bits.length ≤ B)
    (sourceIndex : List Bool) (hsourceLen : sourceIndex.length ≤ B) (i : Fin n)
    (hsourceIndex : addressValue sourceIndex=i.val)
    (v : ℕ→Parts) (hv : WidthBank WellStrength.bank B v) (hg : Good WellStrength.bank v)
    (h8n : (v 8).negative=0) (h8d : (v 8).denominator=1)
    (h9n : (v 9).negative=0) (h9d : (v 9).denominator=1)
    (hscale : (v 4).value ≠ 0)
    (hn : (v 1).value+target v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) ≠ 0)
    (metadata : ℕ→ℕ) (hmetadata : ∀j∈metaIds,(metadata j).bits.length ≤ B)
    (j : Fin m) (index : List Bool) (hindex : addressValue index=j.val) (hlen : index.length ≤ M)
    (hmeta : a.MetadataWidth M) (hfit : P+4096*B+4179 ≤ addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P))
    (hbank : NatAssign.Bank metaIds metadata s.val)
    (hdiagonal : Word s.val 993 diagonalBase) (hdegree : Word s.val 994 degreeBase)
    (hsi : BankArray.Word s.val 998 sourceIndex)
    (ha : BitArray.Represents s.val.memory diagonalBase 4 diagonals)
    (hb : BitArray.Represents s.val.memory degreeBase 2 degrees)
    (hout : a.OutputReady s) (hi : BankArray.Word s.val 999 index) :
    ∃cost t,Executes input tape code cost s t ∧
      cost ≤ 2^22*(B+3)^2+2^184*(P+B+16)^2+2^20*(M+5)^2 ∧
      Ready WellStrength.bank
        (output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) t ∧
      Good WellStrength.bank
        (output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) ∧
      WidthBank WellStrength.bank (P+4096*B+4179)
        (output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) ∧
      output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) 0=
        Parts.literal (WellStrength.numerator P (v 1).value
          (target v (addressValue (diagonals.get i)) (addressValue (degrees.get i))):ℚ) ∧
      (a.set j (output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) 0)).OutputReady t ∧
      t.val.memory=a.writeMemory j
        (output P v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) 0) s.val.memory ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 999 index ∧
      NatAssign.Bank metaIds (prepared 2 2 (prepared 4 8 metadata)) t.val ∧
      (∀k,300 ≤ k→k<1000→k ≠ 995→k ≠ 996→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,z0,z7,b0,f0⟩ := pair_executes diagonals degrees diagonalBase degreeBase B
    hB hdB hgB sourceIndex hsourceLen i hsourceIndex v hv hg metadata hmetadata input tape s hr
    hout.scratch hout.seven hbank hdiagonal hdegree hsi ha hb
  have scale0 : (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) 4).value ≠ 0 := by
    rwa [pairValues_preserves _ _ _ 4 (by decide) (by decide)]
  have target0 := read_target v (addressValue (diagonals.get i)) (addressValue (degrees.get i))
    h8n h8d h9n h9d
  have nonzero0 :
      (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i)) 1).value+
        WellTarget.target .original (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) ≠ 0 := by
    rwa [pairValues_preserves _ _ _ 1 (by decide) (by decide),target0]
  have out0 : a.OutputReady u := by
    apply hout.transfer f0.memory _ z0 z7
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> exact f0.metadata _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c1,t,e1,hc1,r1,g1,w1,value1,out1,memory1,z1,p1,index1,_,_,_,f1⟩ :=
    WellTarget.write_executes a .original P B M hB hP _ w0 g0 scale0 nonzero0 j index hindex hlen
      hmeta hfit hsep input tape u r0 (read_clean hz f0)
      (word_of_eq (f0.metadata 144 (by decide) (by decide) (by decide) (by decide)) hp) out0
      (BankArray.word_of_eq (f0.metadata 999 (by decide) (by decide) (by decide) (by decide)) hi)
  rw [pairValues_preserves _ _ _ 1 (by decide) (by decide),target0] at value1
  refine ⟨c0+c1,t,e0.seq e1,by omega,r1,g1,w1,value1,out1,?_,z1,p1,index1,?_,?_⟩
  · rw [memory1,f0.memory]
    rfl
  · intro k hk
    have bounds : 300 ≤ k ∧ k<1000 := by
      simp only [metaIds,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact word_of_eq (f1 k bounds.1 bounds.2) (b0 k hk)
  · intro k hk hk' h995 h996
    exact (f1 k hk hk').trans (f0.metadata k (by omega) hk' h995 h996)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellOriginalWrite
