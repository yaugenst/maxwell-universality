import Maxwell.Continuum.StoredIntegerStep
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! A fixed counted program serializes a stored integer array in ascending
index order. Its loop count and array contents are runtime data. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def stream (z : ℕ→ℤ) (n : ℕ) : List Bool := (List.range n).flatMap (fun j => Codec.int (z j))
def loopCode : Code := countedProgram 201 stepCode
def loopCost (n B len : ℕ) : ℕ := (n+1)*(13*len+15)+n*(2^23*(B+5)^2)

theorem stream_succ (z : ℕ→ℤ) (j : ℕ) :
    stream z (j+1)=stream z j++Codec.int (z j) := by simp [stream,List.range_succ]

structure State {n : ℕ} (a : Table n) (z : ℕ→ℤ) (B j : ℕ)
    (initialOutput : List Bool) (values : ℕ→Parts) (s : Store) : Prop where
  ready : Ready slots values s
  width : WidthBank slots B values
  table : a.Ready s
  index : RationalAccumulator.Word s.val 728 j
  one : RationalAccumulator.Word s.val 727 1
  output : s.val.output=(stream z j).reverse++initialOutput

theorem State.count_frame {n B j : ℕ} {a : Table n} {z : ℕ→ℤ} {out : List Bool}
    {values : ℕ→Parts} {s t : Store} (h : State a z B j out values s) (f : CountedShifted.Frame 201 s t) :
    State a z B j out values t := by
  refine ⟨h.ready.count_frame slots values 201 (outside_workspace _ _ (by decide)) f,
    h.width,h.table.count_frame f,?_,?_,f.2.2.2.2.1.trans h.output⟩
  · exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 728 (by decide)) h.index
  · exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 727 (by decide)) h.one

theorem loop_executes {n : ℕ} (a : Table n) (z : ℕ→ℤ)
    (hc : ∀i:Fin n,a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (hnB : n.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hn : addressValue xs=n) (s : Store) (values : ℕ→Parts)
    (hstate : State a z B 0 s.val.output values s)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin) :
    ∃cost t word values,Executes input tape loopCode cost s t ∧ cost≤loopCost n B xs.length ∧
      State a z B n s.val.output values t ∧ t.val.tapes 201=BitTape.shifted word origin ∧
      word.length=xs.length := by
  let inv : ℕ→Store→Prop := fun r t => r≤n ∧ ∃values,State a z B (n-r) s.val.output values t
  have stable : ∀r u v,CountedShifted.Frame 201 u v → inv r u → inv r v := by
    intro r u v f h
    obtain ⟨v,hv⟩ := h.2
    exact ⟨h.1,v,hv.count_frame f⟩
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃cost t,Executes input tape stepCode cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^23*(B+5)^2 := by
    intro r ys st hh word _ _
    obtain ⟨v,hv⟩ := hh.2
    have hj : n-(r+1)<n := by have := hh.1;omega
    have he : n-(r+1)+1=n-r := by have := hh.1;omega
    have hbits : (n-(r+1)).bits.length≤B := by
      have h := Nat.size_le_size (Nat.sub_le n (r+1))
      have hb : (n-(r+1)).bits.length≤n.bits.length := by simpa only [Nat.size_eq_bits_len] using h
      exact hb.trans hnB
    obtain ⟨c,t,ex,hcst,rt,at',wt,out,index,one,_,keep⟩ := step_executes a z hc B hm
      ⟨n-(r+1),hj⟩ hbits v hv.width input tape st hv.ready hv.table hv.index hv.one
    refine ⟨c,t,ex,⟨by omega,Function.update v 0 (a.get ⟨n-(r+1),hj⟩),⟨rt,wt,at',?_,one,?_⟩⟩,
      (keep 201 (by decide) (by decide) (by decide)).trans word,hcst⟩
    · simpa only [he] using index
    · rw [out,hv.output,←he,stream_succ,List.reverse_append,List.append_assoc]
  obtain ⟨cost,t,word,ex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin stepCode
    input tape xs.length inv (fun _ => 2^23*(B+5)^2) stable step n xs s hn hcount rfl
      ⟨le_rfl,values,by simpa only [Nat.sub_self] using hstate⟩
  obtain ⟨v,hv⟩ := hfinal.2
  exact ⟨cost,t,word,v,ex,by simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost,
    by simpa only [Nat.sub_zero] using hv,hword,hl⟩

#print axioms loop_executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
