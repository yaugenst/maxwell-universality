import Maxwell.Continuum.StoredDecoderStart
import Maxwell.Continuum.StoredGeometryEmit
import Maxwell.Continuum.StoredNaturalEmission

/-! Complete executed decoder-description suffix: initialize its cursors
from retained source words, emit the five runtime header fields, and read
and serialize every singleton row from the produced arrays. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def headerPorts : List ℕ:=[500,4701,4702,4703,500]
def descriptionCode : Code:=.seq startCode (.seq (StoredNatural.code headerPorts) loopCode)
def descriptionWork : Finset ℕ:=startWork∪loopWork

theorem State.emit_frame {n J j : ℕ} {p : Plan n J} {gv v : ℕ→ℕ} {rv : ℕ→Parts}
    {s t : Store} (h : State p j gv v rv s) (f : EmitNatural.Frame s t):State p j gv v rv t:=by
  have keep (k : ℕ):=congrFun f.2.2.2.2 k
  have geometry:=h.geometry.of_tapes f.2.2.1 f.2.2.2.2
  refine ⟨geometry,h.table.storage_frame f.2.2.1 (fun k _=>keep k) geometry.ready.scratch geometry.ready.seven,
    ⟨fun k hk=>word_of_eq (keep k) (h.raw.1 k hk),fun k hk=>blank_of_eq (keep k) (h.raw.2 k hk)⟩,
    h.rawWidth,word_of_eq (keep 728) h.index,word_of_eq (keep 727) h.one,
    fun k hk=>word_of_eq (keep k) (h.bank k hk),h.bankWidth,?_,h.fixed,h.cursor⟩
  intro k hk
  obtain ⟨word,hw,stored⟩:=h.workspace k hk
  exact ⟨word,hw,BankArray.word_of_eq (keep k) stored⟩

theorem description_executes {n J : ℕ} (p : Plan n J) (first count oldIndex : ℕ)
    {gv v : ℕ→ℕ} {rv : ℕ→Parts} {s : Store}
    (g : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.geometryConstants gv s)
    (table : p.table.Ready s) (raw : RationalDataflow.Ready StoredInteger.slots rv s)
    (rawWidth : WidthBank StoredInteger.slots p.bankWidth rv)
    (bank : NatAssign.Bank ids v s.val) (bound : ∀k∈ids,(v k).bits.length≤p.bankWidth)
    (fixed : ∀k∈constantPorts,v k=p.constants k)
    (old : WordCleanup.Bounded RationalCanonical.workspace p.workspaceWidth s.val)
    (firstWord : Word s.val 503 first) (countWord : Word s.val 500 count)
    (index : Word s.val 728 oldIndex) (one : Word s.val 727 1)
    (oldCounter : List Bool) (counter : BankArray.Word s.val 972 oldCounter)
    (firstBound : first.bits.length≤p.geometryWidth) (countBound : count.bits.length≤p.geometryWidth)
    (cursorBound : (3*first).bits.length≤p.geometryWidth) (three : p.geometryConstants 969=3)
    (headerValues : ℕ→ℕ) (headerWidth : ∀k∈headerPorts,(headerValues k).bits.length≤p.bankWidth)
    (headerWords : ∀k∈headerPorts,Word s.val k (headerValues k))
    (tableSpan : first+count≤J) (geometrySpan : 3*(first+count)≤n)
    (input : List Bool) (tape : ℕ→Bool):
    ∃cost t gv' v' rv',Executes input tape descriptionCode cost s t ∧
      cost≤2^22*(p.geometryWidth+2)^2+6*oldIndex.bits.length+15*first.bits.length+21+
        (6*oldCounter.length+15*count.bits.length+21)+5*(20*p.bankWidth+24)+1+
        ((count+1)*(13*count.bits.length+15)+count*stepCost p.bankWidth p.workspaceWidth) ∧
      t.val.output=(StoredNatural.bits headerPorts headerValues++rows p first count).reverse++s.val.output ∧
      State p (first+count) gv' v' rv' t ∧
      GeometryOutput.OutputFrame descriptionWork s.val t.val:=by
  obtain ⟨c0,u,gv0,e0,h0,s0,counter0,f0⟩:=start_executes p first count oldIndex g table raw rawWidth bank
    bound fixed old firstWord countWord index one oldCounter counter firstBound countBound cursorBound three input tape
  obtain ⟨c1,w,e1,h1,out1,f1⟩:=StoredNatural.executes headerPorts headerValues p.bankWidth headerWidth input tape u
    (fun k hk=>word_of_eq (f0.tapes k (by
      simp only [headerPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      simp only [startWork,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega)) (headerWords k hk))
  have sw:=s0.emit_frame f1
  obtain ⟨origin,word⟩:=counter0
  obtain ⟨c2,t,word',gv',v',rv',e2,h2,st,out2,_,_,f2⟩:=loop_executes sw tableSpan geometrySpan
    input tape count.bits origin (addressValue_bits _) ((congrFun f1.2.2.2.2 972).trans word)
  refine ⟨c0+(c1+c2),t,gv',v',rv',e0.seq (e1.seq e2),?_,?_,st,⟨
    f2.memory.trans (f1.2.2.1.trans f0.memory),f2.inputHead.trans (f1.2.1.trans f0.inputHead),
    f2.randomCursor.trans (f1.2.2.2.1.trans f0.randomCursor),?_⟩⟩
  · change c1≤5*(20*p.bankWidth+24)+1 at h1
    omega
  · rw [out2,out1,f0.output]
    simp only [List.reverse_append,List.append_assoc]
  · intro i hi
    have hh : i∉startWork ∧i∉loopWork:=by simpa only [descriptionWork,Finset.mem_union,not_or] using hi
    exact (f2.tapes i hh.2).trans ((congrFun f1.2.2.2.2 i).trans (f0.tapes i hh.1))

#print axioms description_executes
end Maxwell.Continuum.DecoderRow
