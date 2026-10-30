import Maxwell.Continuum.StoredDyadicStream
import Maxwell.Continuum.StoredIntegerCleanup

/-! Literal fixed-precision dyadic array serialization, including precision
and length headers and all runtime arithmetic, reads and output bits. -/
namespace Maxwell.Continuum.RationalDataflow.StoredDyadic
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
open StoredInteger (slots setupCode clearCode controlChanged setup_executes clear_executes
  ready_control_frame table_control_frame ready_emit_frame table_emit_frame)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def arrayBits {P : ℕ} (d : ℕ→Dyadic P) (n : ℕ) : List Bool :=
  Codec.nat P++Codec.nat n++stream d n
def arrayCode : Code := .seq setupCode (.seq (EmitNatural.code 726)
  (.seq (EmitNatural.code 201) (.seq loopCode clearCode)))
def arrayCost (n P B : ℕ) : ℕ := 2^152*(n+1)*(P+B+6)^2

theorem clean_control_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame (insert 201 controlChanged) s.val t.val) : DyadicFloor.Clean t.val := by
  have dis : Disjoint (insert 4 (DyadicFloor.extraIds∪NaturalQuotient.workPorts))
      (insert 201 controlChanged) := by decide
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4
    (fun hh=>Finset.disjoint_left.mp dis (by simp) hh)) h.1,?_⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i
    (fun hh=>Finset.disjoint_left.mp dis (Finset.mem_insert_of_mem hi) hh)) (h.2 i hi)

theorem clean_emit_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : EmitNatural.Frame s t) : DyadicFloor.Clean t.val :=
  ⟨RationalAccumulator.blank_of_eq (congrFun f.2.2.2.2 4) h.1,
    fun i hi=>RationalAccumulator.blank_of_eq (congrFun f.2.2.2.2 i) (h.2 i hi)⟩

theorem array_executes {n P : ℕ} (a : Table n) (d : ℕ→Dyadic P)
    (hc : ∀i:Fin n,(a.get i).Valid ∧ (a.get i).value=(d i.val).value)
    (B : ℕ) (hm : a.MetadataWidth B) (hnB : n.bits.length≤B) (hPB : P.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots (registerWidth P B) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hcount : Word s.val 201 n) (hprecision : Word s.val 726 P)
    (hpower : Word s.val 144 (2^P)) (hclean : DyadicFloor.Clean s.val)
    (h727 : Blank s.val 727) (h728 : Blank s.val 728) :
    ∃cost t values,Executes input tape arrayCode cost s t ∧ cost≤arrayCost n P B ∧
      Ready slots values t ∧ WidthBank slots (registerWidth P B) values ∧ a.Ready t ∧
      t.val.output=(arrayBits d n).reverse++s.val.output ∧
      Word t.val 726 P ∧ Word t.val 144 (2^P) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨c0,s0,e0,hc0,one0,index0,zero0,f0⟩ := setup_executes input tape s h727 h728 hr.2
  have r0 := ready_control_frame hr f0 zero0
  have a0 := table_control_frame ha f0 zero0
  have count0 := RationalAccumulator.word_of_eq (f0.tapes 201 (by decide)) hcount
  have precision0 := RationalAccumulator.word_of_eq (f0.tapes 726 (by decide)) hprecision
  have power0 := RationalAccumulator.word_of_eq (f0.tapes 144 (by decide)) hpower
  have clean0 := clean_control_frame hclean (f0.mono (Finset.subset_insert _ _))
  obtain ⟨porigin,pword⟩ := precision0
  obtain ⟨s1,e1,out1,f1⟩ := EmitNatural.executes 726 P porigin input tape s0 pword
  have count1 := RationalAccumulator.word_of_eq (congrFun f1.2.2.2.2 201) count0
  obtain ⟨origin,count1⟩ := count1
  obtain ⟨s2,e2,out2,f2⟩ := EmitNatural.executes 201 n origin input tape s1 count1
  have same (i : ℕ) := (congrFun f2.2.2.2.2 i).trans (congrFun f1.2.2.2.2 i)
  have hstate : State a d B 0 s2.val.output v s2 := by
    refine ⟨ready_emit_frame (ready_emit_frame r0 f1) f2,hv,
      table_emit_frame (table_emit_frame a0 f1) f2,
      RationalAccumulator.word_of_eq (same 728) index0,RationalAccumulator.word_of_eq (same 727) one0,
      RationalAccumulator.word_of_eq (same 726) ⟨porigin,pword⟩,
      RationalAccumulator.word_of_eq (same 144) power0,
      clean_emit_frame (clean_emit_frame clean0 f1) f2,?_⟩
    simp [stream]
  have count2 : s2.val.tapes 201=BitTape.shifted n.bits origin := (congrFun f2.2.2.2.2 201).trans count1
  obtain ⟨c3,s3,word,values,e3,hc3,state3,count3,len3⟩ := loop_executes a d hc B hm hnB
    input tape n.bits origin (addressValue_bits _) s2 v hstate count2
  obtain ⟨c4,t,e4,hc4,clean4,zero4,f4⟩ := clear_executes n word input tape s3 state3.index state3.one
    ⟨origin,count3⟩ state3.ready.2
  have table4 := table_metadata_frame state3.table (insert 201 controlChanged) f4 (by decide) zero4
  have ready4 : Ready slots values t := by
    refine ⟨?_,zero4⟩
    have hd : Disjoint (ids slots) (insert 201 controlChanged) := by decide
    intro i hi
    exact RationalAccumulator.word_of_eq (f4.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh))
      (state3.ready.1 i hi)
  refine ⟨c0+((20*P.bits.length+24)+((20*n.bits.length+24)+(c3+c4))),t,values,
    e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,ready4,state3.width,table4,?_,
    RationalAccumulator.word_of_eq (f4.tapes 726 (by decide)) state3.precision,
    RationalAccumulator.word_of_eq (f4.tapes 144 (by decide)) state3.power,
    clean_control_frame state3.clean f4,clean4⟩
  · rw [len3] at hc4
    unfold loopCost at hc3
    have hlin : B+1≤(P+B+6)^2 :=
      (show B+1≤P+B+6 by omega).trans (Nat.le_self_pow (by decide) _)
    have hsetup : c0+20*P.bits.length+24+20*n.bits.length+24+c4≤2^12*(P+B+6)^2 := by
      nlinarith only [hc0,hc4,hnB,hPB,hlin,Nat.zero_le B]
    have hcount : (n+1)*(13*n.bits.length+15)≤28*(n+1)*(P+B+6)^2 := by
      have hp : 13*n.bits.length+15≤28*(P+B+6)^2 := by nlinarith only [hnB,hlin]
      simpa only [Nat.mul_assoc,Nat.mul_comm 28] using Nat.mul_le_mul_left (n+1) hp
    have hp : (P+B+6)^2≤(n+1)*(P+B+6)^2 := Nat.le_mul_of_pos_left _ (by omega)
    unfold arrayCost
    nlinarith only [hsetup,hc3,hcount,hp]
  · rw [f4.output,state3.output,out2,out1,f0.output]
    simp only [arrayBits,List.reverse_append,List.append_assoc]

theorem array_compiled_run {n P : ℕ} (a : Table n) (d : ℕ→Dyadic P)
    (hc : ∀i:Fin n,(a.get i).Valid ∧ (a.get i).value=(d i.val).value)
    (B : ℕ) (hm : a.MetadataWidth B) (hnB : n.bits.length≤B) (hPB : P.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots (registerWidth P B) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hcount : Word s.val 201 n) (hprecision : Word s.val 726 P)
    (hpower : Word s.val 144 (2^P)) (hclean : DyadicFloor.Clean s.val)
    (h727 : Blank s.val 727) (h728 : Blank s.val 728) :
    ∃t values,
      (runPriced (arrayCode.compile.next input tape) (arrayCost n P B+1) s.val).finished=
        some (t.place arrayCode.size) ∧
      (runPriced (arrayCode.compile.next input tape) (arrayCost n P B+1) s.val).instructions≤arrayCost n P B ∧
      Ready slots values t ∧ WidthBank slots (registerWidth P B) values ∧ a.Ready t ∧
      t.val.output=(arrayBits d n).reverse++s.val.output ∧
      Word t.val 726 P ∧ Word t.val 144 (2^P) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨cost,t,values,ex,hcost,rest⟩ := array_executes a d hc B hm hnB hPB v hv input tape s
    hr ha hcount hprecision hpower hclean h727 h728
  obtain ⟨run,steps⟩ := ex.compiled_run (arrayCost n P B+1) (by omega)
  exact ⟨t,values,run,steps ▸ hcost,rest⟩

#print axioms array_compiled_run
end Maxwell.Continuum.RationalDataflow.StoredDyadic
