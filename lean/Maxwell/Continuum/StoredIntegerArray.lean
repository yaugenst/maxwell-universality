import Maxwell.Continuum.StoredIntegerStream
import Maxwell.Continuum.StoredIntegerCleanup
import Maxwell.Continuum.StoredSerializationFrame

/-! Fixed Boolean serialization of an actual stored integer array, including
its length header, ascending reads, output bits and reusable-port cleanup. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def arrayBits (z : ℕ→ℤ) (n : ℕ) : List Bool := Codec.nat n++stream z n
def arrayCode : Code := .seq setupCode (.seq (EmitNatural.code 201) (.seq loopCode clearCode))
def arrayCost (n B : ℕ) : ℕ := 2^26*(n+1)*(B+5)^2

theorem array_executes {n : ℕ} (a : Table n) (z : ℕ→ℤ)
    (hc : ∀i:Fin n,a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (hnB : n.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hcount : RationalAccumulator.Word s.val 201 n)
    (h727 : Blank s.val 727) (h728 : Blank s.val 728) :
    ∃cost t values,Executes input tape arrayCode cost s t ∧ cost≤arrayCost n B ∧
      Ready slots values t ∧ WidthBank slots B values ∧ a.Ready t ∧
      t.val.output=(arrayBits z n).reverse++s.val.output ∧
      (∀i∈({201,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨c0,s0,e0,hc0,one0,index0,zero0,f0⟩ := setup_executes input tape s h727 h728 hr.2
  have r0 := ready_control_frame hr f0 zero0
  have a0 := table_control_frame ha f0 zero0
  have count0 := RationalAccumulator.word_of_eq (f0.tapes 201 (by decide)) hcount
  obtain ⟨origin,count0⟩ := count0
  obtain ⟨s1,e1,out1,f1⟩ := EmitNatural.executes 201 n origin input tape s0 count0
  have hstate : State a z B 0 s1.val.output v s1 := by
    refine ⟨ready_emit_frame r0 f1,hv,table_emit_frame a0 f1,?_,?_,?_⟩
    · exact RationalAccumulator.word_of_eq (congrFun f1.2.2.2.2 728) index0
    · exact RationalAccumulator.word_of_eq (congrFun f1.2.2.2.2 727) one0
    · simp [stream]
  have count1 : s1.val.tapes 201=BitTape.shifted n.bits origin := (congrFun f1.2.2.2.2 201).trans count0
  obtain ⟨c2,s2,word,values,e2,hc2,state2,count2,len2⟩ := loop_executes a z hc B hm hnB
    input tape n.bits origin (addressValue_bits _) s1 v hstate count1
  obtain ⟨c3,t,e3,hc3,clean3,zero3,f3⟩ := clear_executes n word input tape s2 state2.index state2.one
    ⟨origin,count2⟩ state2.ready.2
  have table3 := table_metadata_frame state2.table (insert 201 controlChanged) f3 (by decide) zero3
  have ready3 : Ready slots values t := by
    refine ⟨?_,zero3⟩
    have hd : Disjoint (ids slots) (insert 201 controlChanged) := by decide
    intro i hi
    exact RationalAccumulator.word_of_eq (f3.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh))
      (state2.ready.1 i hi)
  refine ⟨c0+((20*n.bits.length+24)+(c2+c3)),t,values,e0.seq (e1.seq (e2.seq e3)),?_,
    ready3,state2.width,table3,?_,clean3⟩
  · rw [len2] at hc3
    unfold loopCost at hc2
    have hlin : B+1≤(B+5)^2 := by nlinarith
    have hsetup : c0+20*n.bits.length+24+c3≤2^12*(B+5)^2 := by
      nlinarith only [hc0,hc3,hnB,hlin,Nat.zero_le B]
    have hcount : (n+1)*(13*n.bits.length+15)≤28*(n+1)*(B+5)^2 := by
      have hp : 13*n.bits.length+15≤28*(B+5)^2 := by nlinarith only [hnB,hlin]
      simpa only [Nat.mul_assoc,Nat.mul_comm 28] using Nat.mul_le_mul_left (n+1) hp
    have hp : (B+5)^2≤(n+1)*(B+5)^2 := Nat.le_mul_of_pos_left _ (by omega)
    unfold arrayCost
    nlinarith only [hsetup,hc2,hcount,hp]
  · rw [f3.output,state2.output,out1,f0.output]
    simp only [arrayBits,List.reverse_append,List.append_assoc]

theorem array_compiled_run {n : ℕ} (a : Table n) (z : ℕ→ℤ)
    (hc : ∀i:Fin n,a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (hnB : n.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hcount : RationalAccumulator.Word s.val 201 n)
    (h727 : Blank s.val 727) (h728 : Blank s.val 728) :
    ∃t values,
      (runPriced (arrayCode.compile.next input tape) (arrayCost n B+1) s.val).finished=
        some (t.place arrayCode.size) ∧
      (runPriced (arrayCode.compile.next input tape) (arrayCost n B+1) s.val).instructions≤arrayCost n B ∧
      Ready slots values t ∧ WidthBank slots B values ∧ a.Ready t ∧
      t.val.output=(arrayBits z n).reverse++s.val.output ∧
      (∀i∈({201,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨cost,t,values,ex,hcost,rest⟩ := array_executes a z hc B hm hnB v hv input tape s hr ha hcount h727 h728
  obtain ⟨run,steps⟩ := ex.compiled_run (arrayCost n B+1) (by omega)
  exact ⟨t,values,run,steps ▸ hcost,rest⟩

#print axioms array_compiled_run
end Maxwell.Continuum.RationalDataflow.StoredInteger
