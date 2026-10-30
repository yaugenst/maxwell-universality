import Maxwell.Continuum.StoredBitPayload
import Maxwell.Continuum.StoredIntegerStep

/-! The non-geometric portion of each well record is emitted from its
actual chronological strength table and two retained Boolean payload words.
The strength cursor advances once; both shared payload heads are rewound. -/
namespace Maxwell.Continuum.WellPayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def code : Code := .seq (EmitNatural.code 990)
  (.seq StoredInteger.stepCode (.seq (StoredBitPayload.code 991) (StoredBitPayload.code 992)))

def bits (P : ℕ) (numerator : ℤ) (profile template : List Bool) : List Bool :=
  Codec.nat P++Codec.int numerator++profile++template

structure State {J : ℕ} (strengths : Table J) (P B j : ℕ) (profile template : List Bool)
    (values : ℕ→Parts) (s : Store) : Prop where
  ready : RationalDataflow.Ready StoredInteger.slots values s
  width : WidthBank StoredInteger.slots B values
  table : strengths.Ready s
  index : Word s.val 728 j
  one : Word s.val 727 1
  precision : Word s.val 990 P
  profileWord : BankArray.Word s.val 991 profile
  templateWord : BankArray.Word s.val 992 template

theorem State.emit_frame {J P B j : ℕ} {strengths : Table J} {profile template : List Bool}
    {values : ℕ→Parts} {s t : Store} (h : State strengths P B j profile template values s)
    (f : EmitNatural.Frame s t) : State strengths P B j profile template values t := by
  have keep (i : ℕ) := congrFun f.2.2.2.2 i
  exact ⟨StoredInteger.ready_emit_frame h.ready f,h.width,StoredInteger.table_emit_frame h.table f,
    word_of_eq (keep 728) h.index,word_of_eq (keep 727) h.one,word_of_eq (keep 990) h.precision,
    BankArray.word_of_eq (keep 991) h.profileWord,BankArray.word_of_eq (keep 992) h.templateWord⟩

theorem executes {J : ℕ} (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B)
    (profile template : List Bool) (i : Fin J) (hi : i.val.bits.length≤B)
    (values : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : State strengths P B i.val profile template values s) :
    ∃cost t,Executes input tape code cost s t ∧
      cost≤2^25*(B+5)^2+10*(profile.length+template.length)+100 ∧
      State strengths P B (i.val+1) profile template (Function.update values 0 (strengths.get i)) t ∧
      t.val.output=(bits P (numerators i.val) profile template).reverse++s.val.output ∧
      t.val.memory=s.val.memory ∧
      (∀k,10 ≤ k → k∉cellPorts 0 → k≠728 → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨pOrigin,pword⟩ := h.precision
  obtain ⟨a,e0,o0,f0⟩ := EmitNatural.executes 990 P pOrigin input tape s pword
  have ha := h.emit_frame f0
  obtain ⟨c1,b,e1,hc1,r1,a1,w1,o1,index1,one1,mem1,keep1⟩ := StoredInteger.step_executes strengths numerators hc
    B hm i hi values ha.width input tape a ha.ready ha.table ha.index ha.one
  have hb : State strengths P B (i.val+1) profile template (Function.update values 0 (strengths.get i)) b := by
    refine ⟨r1,w1,a1,index1,one1,?_,?_,?_⟩
    · exact word_of_eq (keep1 990 (by decide) (by decide) (by decide)) ha.precision
    · exact BankArray.word_of_eq (keep1 991 (by decide) (by decide) (by decide)) ha.profileWord
    · exact BankArray.word_of_eq (keep1 992 (by decide) (by decide) (by decide)) ha.templateWord
  obtain ⟨profileOrigin,profileWord⟩ := hb.profileWord
  obtain ⟨c,e2,o2,f2⟩ := StoredBitPayload.executes 991 profile profileOrigin input tape b profileWord
  have hcstate := hb.emit_frame f2
  obtain ⟨templateOrigin,templateWord⟩ := hcstate.templateWord
  obtain ⟨t,e3,o3,f3⟩ := StoredBitPayload.executes 992 template templateOrigin input tape c templateWord
  refine ⟨(20*P.bits.length+24)+(c1+((10*profile.length+10)+(10*template.length+10))),t,
    e0.seq (e1.seq (e2.seq e3)),?_,hcstate.emit_frame f3,?_,?_,?_⟩
  · nlinarith only [hc1,hP,Nat.zero_le B]
  · rw [o3,o2,o1,o0]
    simp only [bits,List.reverse_append,List.append_assoc]
  · exact f3.2.2.1.trans (f2.2.2.1.trans (mem1.trans f0.2.2.1))
  · intro k hk hcell hindex
    exact (congrFun f3.2.2.2.2 k).trans ((congrFun f2.2.2.2.2 k).trans
      ((keep1 k hk hcell hindex).trans (congrFun f0.2.2.2.2 k)))

#print axioms executes
end Maxwell.Continuum.WellPayload
