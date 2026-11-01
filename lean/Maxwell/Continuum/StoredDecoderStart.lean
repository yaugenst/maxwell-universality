import Maxwell.Continuum.StoredDecoderLoop
import Maxwell.Continuum.StoredReadoutPrepare
import Maxwell.Cost.BankArray.Frame

/-! Decoder traversal cursors and its countdown are initialized by charged
copies from the retained source dimension and circuit-size words. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def startCode : Code:=.seq GeometryOutput.Readout.prepareCode
  (.seq (WordReplace.code 503 728) (WordReplace.code 500 972))
def startWork : Finset ℕ:={0,1,2,3,971,989,728,972}

theorem start_executes {n J : ℕ} (p : Plan n J) (first count oldIndex : ℕ)
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
    (input : List Bool) (tape : ℕ→Bool):
    ∃cost t gv',Executes input tape startCode cost s t ∧
      cost≤2^22*(p.geometryWidth+2)^2+6*oldIndex.bits.length+15*first.bits.length+21+
        (6*oldCounter.length+15*count.bits.length+21) ∧
      State p first gv' v rv t ∧Word t.val 972 count ∧
      BinaryPrecision.Frame startWork s.val t.val:=by
  obtain ⟨c0,u,e0,h0,gu,f0⟩:=GeometryOutput.Readout.prepare_executes g first count firstBound countBound
    cursorBound three firstWord countWord input tape
  obtain ⟨w,e1,iw,f1⟩:=WordReplace.executes 503 728 (by decide) input tape first.bits oldIndex.bits u
    (word_of_eq (f0.tapes 503 (by decide)) firstWord) (word_of_eq (f0.tapes 728 (by decide)) index)
  obtain ⟨t,e2,ct,f2⟩:=WordReplace.executes 500 972 (by decide) input tape count.bits oldCounter w
    (word_of_eq (f1.2.2.2.2.2.1 500 (by decide)) (word_of_eq (f0.tapes 500 (by decide)) countWord))
    (BankArray.word_of_eq ((f1.2.2.2.2.2.1 972 (by decide)).trans (f0.tapes 972 (by decide))) counter)
  have keep (k : ℕ) (hk : k≠728) (hc : k≠972):t.val.tapes k=u.val.tapes k:=
    (f2.2.2.2.2.2.1 k hc).trans (f1.2.2.2.2.2.1 k hk)
  have frame : BinaryPrecision.Frame startWork s.val t.val:=by
    refine ⟨f2.1.trans (f1.1.trans f0.address),f2.2.1.trans (f1.2.1.trans f0.inputHead),
      f2.2.2.1.trans (f1.2.2.1.trans f0.memory),f2.2.2.2.1.trans (f1.2.2.2.1.trans f0.randomCursor),
      f2.2.2.2.2.1.trans (f1.2.2.2.2.1.trans f0.output),?_⟩
    intro k hk
    have neq : k≠728 ∧k≠972:=by
      simp only [startWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hk;tauto
    exact (keep k neq.1 neq.2).trans (f0.tapes k (fun hm=>hk ((by decide :
      ({0,1,2,3,971,989}:Finset ℕ)⊆startWork) hm)))
  have scratch : BankArray.Scratch t.val:=gu.ready.scratch.of_tapes
    (fun k hk=>keep k (by omega) (by omega))
  have seven : Blank t.val 7:=blank_of_eq (keep 7 (by decide) (by decide)) gu.ready.seven
  have gt : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.geometryConstants
      (GeometryOutput.Readout.prepared gv first count) t:=by
    apply gu.storage_frame (f2.2.2.1.trans f1.2.2.1) _ (keep 962 (by decide) (by decide)) scratch seven
    intro k hk
    have lo:=GeometryOutput.ids_ge k hk
    have high : k≤989:=by simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk;omega
    have notCounter : k≠972:=by simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk;omega
    exact keep k (by omega) notCounter
  have tableT:=table.storage_frame frame.memory (fun k hk=>frame.tapes k (fun hm=>Finset.disjoint_left.mp
    (by decide : Disjoint ({200,202,203,204,205}:Finset ℕ) startWork) hk hm)) scratch seven
  have zero : NatAssign.Scratch t.val:=by
    intro k hk
    exact blank_of_eq (keep k (by omega) (by omega)) (by
      interval_cases k
      · exact gu.ready.scratch.1
      · exact gu.ready.scratch.2.1
      · exact gu.ready.scratch.2.2.1
      · exact gu.ready.scratch.2.2.2.1)
  refine ⟨c0+((6*oldIndex.bits.length+15*first.bits.length+21)+(6*oldCounter.length+15*count.bits.length+21)),
    t,_,e0.seq (e1.seq e2),by omega,⟨gt,tableT,⟨?_,zero⟩,rawWidth,
      word_of_eq (f2.2.2.2.2.2.1 728 (by decide)) iw,word_of_eq (frame.tapes 727 (by decide)) one,
      ?_,bound,?_,fixed,?_⟩,ct,frame⟩
  · intro k hk
    exact word_of_eq (frame.tapes k (fun hm=>Finset.disjoint_left.mp
      (by decide : Disjoint (RationalDataflow.ids StoredInteger.slots) startWork) hk hm)) (raw.1 k hk)
  · intro k hk
    exact word_of_eq (frame.tapes k (fun hm=>Finset.disjoint_left.mp
      (by decide : Disjoint ids startWork) hk hm)) (bank k hk)
  · intro k hk
    by_cases small : k<4
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (zero k small)⟩
    obtain ⟨word,hw,stored⟩:=old k hk
    refine ⟨word,hw,BankArray.word_of_eq (frame.tapes k ?_) stored⟩
    simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [startWork,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  · simp only [GeometryOutput.Readout.prepared,Function.update_of_ne (by decide : (971:ℕ)≠989),
      Function.update_self]

#print axioms start_executes
end Maxwell.Continuum.DecoderRow
