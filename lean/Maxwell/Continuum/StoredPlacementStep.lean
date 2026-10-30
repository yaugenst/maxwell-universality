import Maxwell.Continuum.StoredIntegerStep

/-! A placement is serialized by reading its three stored integer coordinates
and then emitting its common runtime scale. No coordinate is embedded in code. -/
namespace Maxwell.Continuum.RationalDataflow.StoredPlacement
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open StoredInteger
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def recordBits (z : ℕ→ℤ) (L i : ℕ) : List Bool :=
  Codec.int (z (3*i))++Codec.int (z (3*i+1))++Codec.int (z (3*i+2))++Codec.nat L

def stepCode : Code := .seq StoredInteger.stepCode (.seq StoredInteger.stepCode
  (.seq StoredInteger.stepCode (EmitNatural.code 726)))

theorem step_executes {J : ℕ} (a : Table (3*J)) (z : ℕ→ℤ)
    (hc : ∀i:Fin (3*J),a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (hsize : (3*J).bits.length≤B)
    (L : ℕ) (hL : L.bits.length≤B) (i : Fin J)
    (v : ℕ→Parts) (hv : WidthBank slots B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hindex : RationalAccumulator.Word s.val 728 (3*i.val))
    (hone : RationalAccumulator.Word s.val 727 1)
    (hscale : RationalAccumulator.Word s.val 726 L) :
    ∃cost t values,Executes input tape stepCode cost s t ∧ cost≤2^25*(B+5)^2 ∧
      Ready slots values t ∧ a.Ready t ∧ WidthBank slots B values ∧
      t.val.output=(recordBits z L i.val).reverse++s.val.output ∧
      RationalAccumulator.Word t.val 728 (3*(i.val+1)) ∧
      RationalAccumulator.Word t.val 727 1 ∧ RationalAccumulator.Word t.val 726 L ∧
      t.val.memory=s.val.memory ∧
      (∀k,10≤k → k∉cellPorts 0 → k≠728 → t.val.tapes k=s.val.tapes k) := by
  have hj := i.isLt
  let i0 : Fin (3*J) := ⟨3*i.val,by omega⟩
  let i1 : Fin (3*J) := ⟨3*i.val+1,by omega⟩
  let i2 : Fin (3*J) := ⟨3*i.val+2,by omega⟩
  have hbits (j : Fin (3*J)) : j.val.bits.length≤B := by
    have h := Nat.size_le_size (Nat.le_of_lt j.isLt)
    have hb : j.val.bits.length≤(3*J).bits.length := by simpa only [Nat.size_eq_bits_len] using h
    exact hb.trans hsize
  obtain ⟨c0,s0,e0,hc0,r0,a0,w0,out0,index0,one0,mem0,keep0⟩ :=
    StoredInteger.step_executes a z hc B hm i0 (hbits i0) v hv input tape s hr ha hindex hone
  let v0 := Function.update v 0 (a.get i0)
  obtain ⟨c1,s1,e1,hc1,r1,a1,w1,out1,index1,one1,mem1,keep1⟩ :=
    StoredInteger.step_executes a z hc B hm i1 (hbits i1) v0 w0 input tape s0 r0 a0 index0 one0
  let v1 := Function.update v0 0 (a.get i1)
  have index1' : RationalAccumulator.Word s1.val 728 i2.val := by
    simpa only [i1,i2,Nat.add_assoc] using index1
  obtain ⟨c2,s2,e2,hc2,r2,a2,w2,out2,index2,one2,mem2,keep2⟩ :=
    StoredInteger.step_executes a z hc B hm i2 (hbits i2) v1 w1 input tape s1 r1 a1 index1' one1
  have scale2 := RationalAccumulator.word_of_eq
    ((keep2 726 (by decide) (by decide) (by decide)).trans
      ((keep1 726 (by decide) (by decide) (by decide)).trans
        (keep0 726 (by decide) (by decide) (by decide)))) hscale
  obtain ⟨origin,word⟩ := scale2
  obtain ⟨t,e3,out3,f3⟩ := EmitNatural.executes 726 L origin input tape s2 word
  refine ⟨c0+(c1+(c2+(20*L.bits.length+24))),t,Function.update v1 0 (a.get i2),
    e0.seq (e1.seq (e2.seq e3)),?_,ready_emit_frame r2 f3,table_emit_frame a2 f3,w2,?_,?_,
    RationalAccumulator.word_of_eq (congrFun f3.2.2.2.2 727) one2,
    RationalAccumulator.word_of_eq (congrFun f3.2.2.2.2 726) ⟨origin,word⟩,
    f3.2.2.1.trans (mem2.trans (mem1.trans mem0)),?_⟩
  · have hh : B+1≤(B+5)^2 := by nlinarith
    nlinarith only [hc0,hc1,hc2,hL,hh]
  · rw [out3,out2,out1,out0]
    simp only [recordBits,i0,i1,i2,List.reverse_append,List.append_assoc]
  · have he : i2.val+1=3*(i.val+1) := by simp only [i2];omega
    exact RationalAccumulator.word_of_eq (congrFun f3.2.2.2.2 728) (he ▸ index2)
  · intro k hk hcell hindex
    exact (congrFun f3.2.2.2.2 k).trans ((keep2 k hk hcell hindex).trans
      ((keep1 k hk hcell hindex).trans (keep0 k hk hcell hindex)))

#print axioms step_executes
end Maxwell.Continuum.RationalDataflow.StoredPlacement
