import Maxwell.Continuum.StoredSourceLoopState

/-! A fixed counted program emits the requested source records
using only actual packed geometry and the retained original rational archive. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def rows {n : ℕ} (p : Plan n) (first count : ℕ):List Bool:=
  (List.range count).flatMap (fun j=>rowBits p (first+j))
def loopCode : Code:=countedProgram 972 stepCode
def loopWork : Finset ℕ:=insert 972 stepWork

theorem rows_succ {n : ℕ} (p : Plan n) (first count : ℕ):
    rows p first (count+1)=rows p first count++rowBits p (first+count):=by
  simp [rows,List.range_succ]

theorem loop_executes {n first count : ℕ} {p : Plan n} {gv : ℕ→ℕ} {v : ℕ→Parts}
    {s : Store} (h : State p first gv v s)
    (span : first+count≤p.source.length)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (countValue : addressValue xs=count) (counter : s.val.tapes 972=BitTape.shifted xs origin):
    ∃cost t word gv' v',Executes input tape loopCode cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*stepCost p ∧
      State p (first+count) gv' v' t ∧
      t.val.output=(rows p first count).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧word.length=xs.length ∧
      GeometryOutput.OutputFrame loopWork s.val t.val:=by
  let inv : ℕ→Store→Prop:=fun remaining t=>remaining≤count ∧∃gv' v',
    State p (first+(count-remaining)) gv' v' t ∧
      t.val.output=(rows p first (count-remaining)).reverse++s.val.output ∧
      GeometryOutput.OutputFrame loopWork s.val t.val
  have stable : ∀r a b,CountedShifted.Frame 972 a b→inv r a→inv r b:=by
    intro r a b f hh
    obtain ⟨gv',v',state,out,frame⟩:=hh.2
    refine ⟨hh.1,gv',v',state.count_frame f,f.2.2.2.2.1.trans out,
      ⟨f.2.2.1.trans frame.memory,f.2.1.trans frame.inputHead,f.2.2.2.1.trans frame.randomCursor,?_⟩⟩
    intro k hk
    have hn : k≠972:=by intro he;subst k;exact hk (Finset.mem_insert_self _ _)
    exact (f.2.2.2.2.2.1 k hn).trans (frame.tapes k hk)
  have step : ∀r ys a,inv (r+1) a→a.val.tapes 972=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃c b,Executes input tape stepCode c a b ∧inv r b ∧
        b.val.tapes 972=BitTape.shifted ys origin ∧c≤stepCost p:=by
    intro r ys a hh word _ _
    obtain ⟨gv',v',state,out,frame⟩:=hh.2
    have hj : first+(count-(r+1))<p.source.length:=by have :=hh.1;omega
    have next : count-(r+1)+1=count-r:=by have :=hh.1;omega
    obtain ⟨c,b,gv'',ex,hc,st,outStep,frameStep⟩:=state.step hj input tape
    refine ⟨c,b,ex,⟨by omega,gv'',resetValues v',?_,?_,?_⟩,?_,hc⟩
    · simpa only [Nat.add_assoc,next] using st
    · rw [outStep,out]
      rw [←next,rows_succ,List.reverse_append,List.append_assoc]
    · refine ⟨frameStep.memory.trans frame.memory,frameStep.inputHead.trans frame.inputHead,
        frameStep.randomCursor.trans frame.randomCursor,?_⟩
      intro k hk
      exact (frameStep.tapes k (fun hm=>hk (Finset.mem_insert_of_mem hm))).trans (frame.tapes k hk)
    · exact (frameStep.tapes 972 (by decide)).trans word
  have initial : inv count s:=by
    refine ⟨le_rfl,gv,v,?_,?_,⟨rfl,rfl,rfl,fun _ _=>rfl⟩⟩
    · simpa only [Nat.sub_self,Nat.add_zero] using h
    · simp only [Nat.sub_self,rows,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,final,wt,wl,_,costBound⟩:=counted_executes_sized 972 origin stepCode
    input tape xs.length inv (fun _=>stepCost p) stable step count xs s
    countValue counter rfl initial
  obtain ⟨gv',v',state,out,frame⟩:=final.2
  exact ⟨cost,t,word,gv',v',ex,
    by simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using costBound,
    by simpa only [Nat.sub_zero] using state,by simpa only [Nat.sub_zero] using out,wt,wl,frame⟩

#print axioms loop_executes
end Maxwell.Continuum.SourcePayload
