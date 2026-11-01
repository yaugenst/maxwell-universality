import Maxwell.Continuum.StoredDecoderLoopState

/-! A fixed counted program emits the requested consecutive decoder rows
using only actual packed-geometry and strength-table storage. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def rowBits {n J : ℕ} (p : Plan n J) (j : ℕ):List Bool:=
  if h:j<J then bits (rowValues p.data p.constants j (p.table.get ⟨j,h⟩)) else []
def rows {n J : ℕ} (p : Plan n J) (first count : ℕ):List Bool:=
  (List.range count).flatMap (fun j=>rowBits p (first+j))
def loopCode : Code:=countedProgram 972 stepCode
def loopWork : Finset ℕ:=insert 972 stepWork

theorem rows_succ {n J : ℕ} (p : Plan n J) (first count : ℕ):
    rows p first (count+1)=rows p first count++rowBits p (first+count):=by
  simp [rows,List.range_succ]

theorem loop_executes {n J first count : ℕ} {p : Plan n J} {gv v : ℕ→ℕ} {rv : ℕ→Parts}
    {s : Store} (h : State p first gv v rv s)
    (tableSpan : first+count≤J) (geometrySpan : 3*(first+count)≤n)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (countValue : addressValue xs=count) (counter : s.val.tapes 972=BitTape.shifted xs origin):
    ∃cost t word gv' v' rv',Executes input tape loopCode cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*stepCost p.bankWidth p.workspaceWidth ∧
      State p (first+count) gv' v' rv' t ∧
      t.val.output=(rows p first count).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧word.length=xs.length ∧
      GeometryOutput.OutputFrame loopWork s.val t.val:=by
  let inv : ℕ→Store→Prop:=fun remaining t=>remaining≤count ∧∃gv' v' rv',
    State p (first+(count-remaining)) gv' v' rv' t ∧
      t.val.output=(rows p first (count-remaining)).reverse++s.val.output ∧
      GeometryOutput.OutputFrame loopWork s.val t.val
  have stable : ∀r a b,CountedShifted.Frame 972 a b→inv r a→inv r b:=by
    intro r a b f hh
    obtain ⟨gv',v',rv',state,out,frame⟩:=hh.2
    refine ⟨hh.1,gv',v',rv',state.count_frame f,f.2.2.2.2.1.trans out,
      ⟨f.2.2.1.trans frame.memory,f.2.1.trans frame.inputHead,f.2.2.2.1.trans frame.randomCursor,?_⟩⟩
    intro k hk
    have hn : k≠972:=by intro he;subst k;exact hk (Finset.mem_insert_self _ _)
    exact (f.2.2.2.2.2.1 k hn).trans (frame.tapes k hk)
  have step : ∀r ys a,inv (r+1) a→a.val.tapes 972=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃c b,Executes input tape stepCode c a b ∧inv r b ∧
        b.val.tapes 972=BitTape.shifted ys origin ∧c≤stepCost p.bankWidth p.workspaceWidth:=by
    intro r ys a hh word _ _
    obtain ⟨gv',v',rv',state,out,frame⟩:=hh.2
    have hj : first+(count-(r+1))<J:=by have :=hh.1;omega
    have span : 3*(first+(count-(r+1)))+3≤n:=by have :=hh.1;omega
    have next : count-(r+1)+1=count-r:=by have :=hh.1;omega
    obtain ⟨c,b,gv'',v'',rv'',ex,hc,st,outStep,frameStep⟩:=state.step hj span input tape
    refine ⟨c,b,ex,⟨by omega,gv'',v'',rv'',?_,?_,?_⟩,?_,hc⟩
    · simpa only [Nat.add_assoc,next] using st
    · rw [outStep,out]
      have rowEq : bits (rowValues p.data p.constants (first+(count-(r+1)))
          (p.table.get ⟨first+(count-(r+1)),hj⟩))=rowBits p (first+(count-(r+1))):=by
        rw [rowBits,dite_eq_left hj]
      rw [rowEq,←next,rows_succ,List.reverse_append,List.append_assoc]
    · refine ⟨frameStep.memory.trans frame.memory,frameStep.inputHead.trans frame.inputHead,
        frameStep.randomCursor.trans frame.randomCursor,?_⟩
      intro k hk
      exact (frameStep.tapes k (fun hm=>hk (Finset.mem_insert_of_mem hm))).trans (frame.tapes k hk)
    · exact (frameStep.tapes 972 (by decide)).trans word
  have initial : inv count s:=by
    refine ⟨le_rfl,gv,v,rv,?_,?_,⟨rfl,rfl,rfl,fun _ _=>rfl⟩⟩
    · simpa only [Nat.sub_self,Nat.add_zero] using h
    · simp only [Nat.sub_self,rows,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,final,wt,wl,_,costBound⟩:=counted_executes_sized 972 origin stepCode
    input tape xs.length inv (fun _=>stepCost p.bankWidth p.workspaceWidth) stable step count xs s
    countValue counter rfl initial
  obtain ⟨gv',v',rv',state,out,frame⟩:=final.2
  exact ⟨cost,t,word,gv',v',rv',ex,
    by simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using costBound,
    by simpa only [Nat.sub_zero] using state,by simpa only [Nat.sub_zero] using out,wt,wl,frame⟩

#print axioms loop_executes
end Maxwell.Continuum.DecoderRow
