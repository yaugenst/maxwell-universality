import Maxwell.Continuum.StoredPlacementStep
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! Fixed ascending traversal of a flattened coordinate table. The record
count, all coordinates, and the common length are runtime inputs. -/
namespace Maxwell.Continuum.RationalDataflow.StoredPlacement
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open StoredInteger (slots)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def stream (z : ℕ→ℤ) (L J : ℕ) : List Bool := (List.range J).flatMap (recordBits z L)
def loopCode : Code := countedProgram 201 stepCode
def loopCost (J B len : ℕ) : ℕ := (J+1)*(13*len+15)+J*(2^25*(B+5)^2)

theorem stream_succ (z : ℕ→ℤ) (L j : ℕ) :
    stream z L (j+1)=stream z L j++recordBits z L j := by simp [stream,List.range_succ]

structure State {J : ℕ} (a : Table (3*J)) (z : ℕ→ℤ) (L B j : ℕ)
    (initialOutput : List Bool) (values : ℕ→Parts) (s : Store) : Prop where
  ready : Ready slots values s
  width : WidthBank slots B values
  table : a.Ready s
  index : RationalAccumulator.Word s.val 728 (3*j)
  one : RationalAccumulator.Word s.val 727 1
  scale : RationalAccumulator.Word s.val 726 L
  output : s.val.output=(stream z L j).reverse++initialOutput

theorem State.count_frame {J L B j : ℕ} {a : Table (3*J)} {z : ℕ→ℤ} {out : List Bool}
    {values : ℕ→Parts} {s t : Store} (h : State a z L B j out values s) (f : CountedShifted.Frame 201 s t) :
    State a z L B j out values t := by
  refine ⟨h.ready.count_frame slots values 201 (outside_workspace _ _ (by decide)) f,
    h.width,h.table.count_frame f,?_,?_,?_,f.2.2.2.2.1.trans h.output⟩
  · exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 728 (by decide)) h.index
  · exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 727 (by decide)) h.one
  · exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 726 (by decide)) h.scale

theorem loop_executes {J : ℕ} (a : Table (3*J)) (z : ℕ→ℤ)
    (hc : ∀i:Fin (3*J),a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (L B : ℕ) (hm : a.MetadataWidth B) (hnB : (3*J).bits.length≤B) (hL : L.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hn : addressValue xs=J) (s : Store) (values : ℕ→Parts)
    (hstate : State a z L B 0 s.val.output values s)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin) :
    ∃cost t word values,Executes input tape loopCode cost s t ∧ cost≤loopCost J B xs.length ∧
      State a z L B J s.val.output values t ∧ t.val.tapes 201=BitTape.shifted word origin ∧
      word.length=xs.length := by
  let inv : ℕ→Store→Prop := fun r t => r≤J ∧ ∃values,State a z L B (J-r) s.val.output values t
  have stable : ∀r u v,CountedShifted.Frame 201 u v → inv r u → inv r v := by
    intro r u v f h
    obtain ⟨v,hv⟩ := h.2
    exact ⟨h.1,v,hv.count_frame f⟩
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃cost t,Executes input tape stepCode cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^25*(B+5)^2 := by
    intro r ys st hh word _ _
    obtain ⟨v,hv⟩ := hh.2
    have hj : J-(r+1)<J := by have := hh.1;omega
    have he : J-(r+1)+1=J-r := by have := hh.1;omega
    obtain ⟨c,t,v',ex,hcst,rt,at',wt,out,index,one,scale,_,keep⟩ := step_executes a z hc B hm hnB
      L hL ⟨J-(r+1),hj⟩ v hv.width input tape st hv.ready hv.table hv.index hv.one hv.scale
    refine ⟨c,t,ex,⟨by omega,v',⟨rt,wt,at',?_,one,scale,?_⟩⟩,
      (keep 201 (by decide) (by decide) (by decide)).trans word,hcst⟩
    · simpa only [he] using index
    · rw [out,hv.output,←he,stream_succ,List.reverse_append,List.append_assoc]
  obtain ⟨cost,t,word,ex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin stepCode
    input tape xs.length inv (fun _ => 2^25*(B+5)^2) stable step J xs s hn hcount rfl
      ⟨le_rfl,values,by simpa only [Nat.sub_self] using hstate⟩
  obtain ⟨v,hv⟩ := hfinal.2
  exact ⟨cost,t,word,v,ex,by simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost,
    by simpa only [Nat.sub_zero] using hv,hword,hl⟩

#print axioms loop_executes
end Maxwell.Continuum.RationalDataflow.StoredPlacement
