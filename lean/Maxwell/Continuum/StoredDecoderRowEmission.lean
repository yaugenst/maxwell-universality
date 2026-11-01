import Maxwell.Continuum.StoredDecoderRowPlan
import Maxwell.Cost.RationalCanonical.PreparedEmission
import Maxwell.Cost.EmitLiteral
import Maxwell.Cost.EmitNatural
import Maxwell.Continuum.StoredGeometryCoordinate

/-! Exact canonical decoder-row bytes from actual coordinate and strength
words. Fraction reduction is executed by the shared Euclidean serializer. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def rowPrefix : List Bool:=Codec.rat 0++Codec.nat 1
def bits (v : ℕ→ℕ):=rowPrefix++Codec.nat (address v)++
  Codec.rat (RationalCanonical.value false (v 1000*v 4707) (v 144*v 4708))
def code : Code:=.seq (NatAssign.code plan)
  (.seq (EmitLiteral.code 30 rowPrefix) (.seq (EmitNatural.code 4800)
    (.seq (.atom (.literal 23 false)) RationalCanonical.preparedCode)))
def work : Finset ℕ:=({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ)∪outputs
def emissionCost (B H : ℕ):=costBound B+(4*rowPrefix.length+1)+
  (20*width B+24)+2+(11*(6*H+4)+1)+100000*(2*width B+2)^3

theorem emit (v : ℕ→ℕ) (B H : ℕ) (hB : 2≤B)
    (bound : ∀i∈ids,(v i).bits.length≤B)
    (positivePower : 0<v 144) (positiveScale : 0<v 4708)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded RationalCanonical.workspace H s.val):
    ∃cost t,Executes input tape code cost s t ∧cost≤emissionCost B H ∧
      t.val.output=(bits v).reverse++s.val.output ∧
      NatAssign.Bank ids (values v) t.val ∧NatAssign.Scratch t.val ∧
      RationalCanonical.NormalizeReady t.val (v 1000*v 4707) (v 144*v 4708) ∧
      GeometryOutput.OutputFrame work s.val t.val:=by
  obtain ⟨c0,a,e0,h0,ba,sa,wa,f0⟩:=executes v B hB bound input tape s bank scratch
  have oldA : WordCleanup.Bounded RationalCanonical.workspace H a.val:=by
    intro i hi
    by_cases small : i<4
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (sa i small)⟩
    · obtain ⟨word,hw,stored⟩:=old i hi
      refine ⟨word,hw,BankArray.word_of_eq (f0.tapes i ?_) stored⟩
      simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,outputs,not_or]
      omega
  let b:=EmitLiteral.finish 30 rowPrefix a
  have e1:=EmitLiteral.executes 30 rowPrefix input tape a
  have f1:=EmitLiteral.finish_frame 30 rowPrefix a
  obtain ⟨origin,word⟩:=ba 4800 (by decide)
  obtain ⟨c,e2,out2,f2⟩:=EmitNatural.executes 4800 (values v 4800) origin input tape b
    ((congrFun f1.2.2.2.2.1 4800).trans word)
  let d:=Store.ofState (c.val.setRegister 23 false)
  have e3 : Executes input tape (.atom (.literal 23 false)) 2 c d:=Executes.literal input tape c 23 false
  have tapesD : d.val.tapes=a.val.tapes:=f2.2.2.2.2.trans f1.2.2.2.2.1
  have num : Word d.val 228 (v 1000*v 4707):=by
    rw [←(result v).2.1]
    exact word_of_eq (congrFun tapesD 228) (ba 228 (by decide))
  have den : Word d.val 229 (v 144*v 4708):=by
    rw [←(result v).2.2]
    exact word_of_eq (congrFun tapesD 229) (ba 229 (by decide))
  have oldD : WordCleanup.Bounded RationalCanonical.workspace H d.val:=by
    intro i hi
    obtain ⟨word,hw,stored⟩:=oldA i hi
    exact ⟨word,hw,BankArray.word_of_eq (congrFun tapesD i) stored⟩
  obtain ⟨c4,t,e4,h4,out4,ready,frame4⟩:=RationalCanonical.prepared_executes input tape false
    (v 1000*v 4707) (v 144*v 4708) H (Nat.mul_pos positivePower positiveScale) d num den oldD
    (by simp [d,Store.ofState,BitRAMState.setRegister])
  have finalBank : NatAssign.Bank ids (values v) t.val:=by
    intro i hi
    by_cases hn : i=228
    · subst i; simpa only [(result v).2.1] using ready.numerator
    by_cases hd : i=229
    · subst i; simpa only [(result v).2.2] using ready.denominator
    apply word_of_eq ((frame4.tapes i ?_).trans (congrFun tapesD i)) (ba i hi)
    simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  refine ⟨c0+((4*rowPrefix.length+1)+((20*(values v 4800).bits.length+24)+(2+c4))),t,
    e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,?_,finalBank,
    fun i hi=>ready.work.scratch i (by omega),ready,?_⟩
  · have hsize : (v 1000*v 4707).size+(v 144*v 4708).size+2≤2*width B+2:=by
      have hn:=wa 228 (by decide)
      have hd:=wa 229 (by decide)
      rw [(result v).2.1] at hn
      rw [(result v).2.2] at hd
      rw [Nat.size_eq_bits_len] at hn hd
      omega
    have hc:=RationalCanonical.costBound_polynomial (v 1000*v 4707) (v 144*v 4708)
    have hp:=Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hsize 3)
    have hx:=wa 4800 (by decide)
    unfold emissionCost
    omega
  · rw [out4]
    change _++c.val.output=_
    rw [out2,EmitLiteral.finish_output,f0.output,(result v).1]
    simp only [bits,List.reverse_append,List.append_assoc]
  · refine ⟨frame4.memory.trans (f2.2.2.1.trans (f1.2.2.1.trans f0.memory)),
      frame4.inputHead.trans (f2.2.1.trans (f1.2.1.trans f0.inputHead)),
      frame4.randomCursor.trans (f2.2.2.2.1.trans (f1.2.2.2.1.trans f0.randomCursor)),?_⟩
    intro i hi
    have hcan : i∉({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ):=
      fun hm=>hi (Finset.mem_union_left _ hm)
    have hcalc : i∉({0,1,2,3}:Finset ℕ)∪outputs:=by
      exact fun hm=>hi ((by decide : ({0,1,2,3}:Finset ℕ)∪outputs⊆work) hm)
    exact (frame4.tapes i hcan).trans ((congrFun tapesD i).trans (f0.tapes i hcalc))

#print axioms emit
end Maxwell.Continuum.DecoderRow
