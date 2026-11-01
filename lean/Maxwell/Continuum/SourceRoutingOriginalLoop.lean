import Maxwell.Continuum.SourceRoutingOriginalPrefix

/-! Finite original-vertex pass driven by the actual count word. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2800000
set_option maxRecDepth 16384

def originalLoopCode (part : Bool) : Code :=
  .seq (CountedShifted.code 1258 (originalStepCode part)) (.call (TapeOps.clear 1258))

def originalLoopCost {q : ℕ} (p : Plan q) (n count : ℕ) : ℕ :=
  (count+1)*(13*count.bits.length+15)+count*originalStepCost p n+6*count.bits.length+4

theorem counter_archive {s t : Store} (frame : CountedShifted.Frame 1258 s t) :
    ArchiveFrame work s.val t.val :=
  ⟨frame.2.1,frame.2.2.2.1,frame.2.2.2.2.1,fun j _ hj=>frame.2.2.2.2.2.1 j (by
    intro h;subst j;exact hj (by simp [work]))⟩

theorem original_loop {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (p : Plan (2*half)) (vertexRoom : v≤half*half)
    (tile : ∀i,data.tile i=finProdFinEquiv.symm (Fin.castLE vertexRoom i))
    (part : Bool) (offset count : ℕ) (bound : offset+count≤v)
    (parts : ∀i : Fin v, offset ≤ i.val → i.val < offset+count → data.part i=part)
    (cursor n : ℕ) (room : cursor+3*count+192≤n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : State data p cursor offset s) (counter : Word s.val 1258 count) :
    ∃steps t,Executes input tape (originalLoopCode part) steps s t ∧
      steps≤originalLoopCost p n count ∧ State data p (cursor+3*count) (offset+count) t ∧
      Blank t.val 1258 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
        (pointsBits p.path.width (originalPrefix data offset count)) ∧
      ArchiveFrame work s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  obtain ⟨origin,word⟩:=counter
  let inv : ℕ→Store→Prop:=fun remaining st=>remaining≤count ∧
    State data p (cursor+3*(count-remaining)) (offset+(count-remaining)) st ∧
    st.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
      (pointsBits p.path.width (originalPrefix data offset (count-remaining))) ∧
    ArchiveFrame work s.val st.val ∧
    Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory st.val.memory
  have stable : ∀r a b,CountedShifted.Frame 1258 a b→inv r a→inv r b:=by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hf.2.2.1.trans hh.2.2.1,
      hh.2.2.2.1.trans (counter_archive hf),by rw [hf.2.2.1];exact hh.2.2.2.2⟩
  have body : ∀r ys a,inv (r+1) a→a.val.tapes 1258=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t,Executes input tape (originalStepCode part) cost a t ∧ inv r t ∧
        t.val.tapes 1258=BitTape.shifted ys origin ∧ cost≤originalStepCost p n := by
    intro r ys a hh hw _
    let k:=count-(r+1)
    have kl : k<count:=by dsimp only [k];have h:=hh.1;omega
    let i : Fin v:=⟨offset+k,by omega⟩
    obtain ⟨cost,t,he,hc,ts,mt,ft,tm⟩:=original_step data p vertexRoom tile i part
      (parts i (by dsimp only [i];omega) (by dsimp only [i];omega))
      (cursor+3*k) n (by omega) input tape a hh.2.1
    have next : k+1=count-r:=by dsimp only [k];have h:=hh.1;omega
    have written : t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
        (pointsBits p.path.width (originalPrefix data offset (count-r))) := by
      rw [mt,hh.2.2.1]
      change MemoryWord.writeBits (MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
        (pointsBits p.path.width (originalPrefix data offset k)))
        (p.path.base+(cursor+3*k)*p.path.width) (pointsBits p.path.width [Gluing.vertexPoint data i])=_
      have append:=write_points_append s.val.memory p.path.base p.path.width cursor
        (originalPrefix data offset k) [Gluing.vertexPoint data i]
      rw [originalPrefix_length data offset k (by omega)] at append
      rw [append,←originalPrefix_succ data offset k (by omega),next]
    have ts' : State data p (cursor+3*(count-r)) (offset+(count-r)) t:=by
      have eqc : cursor+3*(count-r)=cursor+3*k+3:=by omega
      have eqi : offset+(count-r)=i.val+1:=by dsimp only [i];omega
      rw [eqc,eqi]
      exact ts
    exact ⟨cost,t,he,⟨by have h:=hh.1;omega,ts',written,
      hh.2.2.2.1.trans (ft.mono Finset.subset_union_right),hh.2.2.2.2.trans tm⟩,
      (ft.tapes 1258 (by decide) (by decide)).trans hw,hc⟩
  have initial : inv count s:=by
    refine ⟨le_rfl,?_,?_,ArchiveFrame.refl _ _,Tree.Memory.Frame.refl _ _ _⟩
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using state
    · simp only [Nat.sub_self,originalPrefix_zero,pointsBits,List.flatMap_nil,MemoryWord.writeBits]
  obtain ⟨cost,b,finalWord,he,hb,hw,hl,_,hc⟩:=CountedShifted.executes 1258 origin
    (originalStepCode part) input tape inv (fun _=>originalStepCost p n) stable body
    count count.bits s (addressValue_bits count) word initial
  obtain ⟨t,ec,zt,fc⟩:=RuntimeCounter.clear_executes 1258 input tape finalWord origin b hw
  have bs : State data p (cursor+3*count) (offset+count) b:=by
    simpa only [Nat.sub_zero] using hb.2.1
  have ts:=bs.control_frame fc.memory (fun j _ hj=>fc.tapes j (by simpa using hj))
    (RationalAccumulator.word_of_eq (fc.tapes 1257 (by decide)) bs.indexWord)
  refine ⟨cost+(6*finalWord.length+4),t,he.seq ec,?_,ts,zt,?_,
    hb.2.2.2.1.trans ((ArchiveFrame.of_binary fc).mono (by decide)),by rw [fc.memory];exact hb.2.2.2.2⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hc
    rw [hl]
    unfold originalLoopCost
    omega
  · rw [fc.memory]
    simpa only [Nat.sub_zero] using hb.2.2.1

#print axioms original_loop
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
