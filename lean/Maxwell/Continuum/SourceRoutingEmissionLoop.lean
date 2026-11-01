import Maxwell.Continuum.SourceRoutingOriginalLoop
import Maxwell.Continuum.SourceRoutingEmissionPrefix

/-! The active-edge pass performs exactly one actual traversal per edge and
writes its count-prefixed path to consecutive memory words. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2800000
set_option maxRecDepth 16384

def edgeLoopCode : Code :=
  .seq (CountedShifted.code 1258 edgeStepCode) (.call (TapeOps.clear 1258))
def edgeLoopCost {q : ℕ} (p : Plan q) (n count : ℕ) : ℕ :=
  (count+1)*(13*count.bits.length+15)+count*edgeStepCost p n+6*count.bits.length+4

theorem edge_loop {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (p : Plan (2*half)) (edgeRoom : e≤half*(2*half))
    (pair : ∀i,data.pair i=finProdFinEquiv.symm (Fin.castLE edgeRoom i))
    (saved : SourceEmission.Geometry v e)
    (paths : ∀i,saved.paths.get i=EdgeEmission.edge data (EdgeEmission.prepare data) i)
    (n : ℕ) (fits₀ : GeometrySort.Fits p.path.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.path.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.path.history.width (PhaseKeys.last data.colors))
    (room : packedLength saved+1+3072*(2*half)≤n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : State data p (3*v) 0 s) (counter : Word s.val 1258 e) :
    ∃steps t,Executes input tape edgeLoopCode steps s t ∧
      steps≤edgeLoopCost p n e ∧ State data p (packedLength saved) e t ∧ Blank t.val 1258 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+3*v*p.path.width)
        (pathRecordsBits saved p.path.width e) ∧
      ArchiveFrame work s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  obtain ⟨origin,word⟩:=counter
  let inv : ℕ→Store→Prop:=fun remaining st=>remaining≤e ∧
    State data p (pathOffset saved (e-remaining)) (e-remaining) st ∧
    st.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+3*v*p.path.width)
      (pathRecordsBits saved p.path.width (e-remaining)) ∧
    ArchiveFrame work s.val st.val ∧
    Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory st.val.memory
  have stable : ∀r a b,CountedShifted.Frame 1258 a b→inv r a→inv r b:=by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hf.2.2.1.trans hh.2.2.1,
      hh.2.2.2.1.trans (counter_archive hf),by rw [hf.2.2.1];exact hh.2.2.2.2⟩
  have body : ∀r ys a,inv (r+1) a→a.val.tapes 1258=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t,Executes input tape edgeStepCode cost a t ∧ inv r t ∧
        t.val.tapes 1258=BitTape.shifted ys origin ∧ cost≤edgeStepCost p n := by
    intro r ys a hh hw _
    let i : Fin e:=⟨e-(r+1),by have h:=hh.1;omega⟩
    have space:=pathOffset_le_end saved i.val
    obtain ⟨cost,t,he,hc,ts,mt,ft,tm⟩:=edge_step data p edgeRoom pair i (pathOffset saved i.val)
      n fits₀ fits₁ fits₂ (by omega) input tape a hh.2.1
    have next : i.val+1=e-r:=by dsimp only [i];have h:=hh.1;omega
    rw [←paths i,←pathOffset_succ,next] at ts
    have written : t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+3*v*p.path.width)
        (pathRecordsBits saved p.path.width (e-r)):=by
      rw [mt,hh.2.2.1,←paths i]
      change MemoryWord.writeBits (MemoryWord.writeBits s.val.memory (p.path.base+3*v*p.path.width)
        (pathRecordsBits saved p.path.width i.val)) (p.path.base+pathOffset saved i.val*p.path.width)
        (packedEdgeBits p.path.width (saved.paths.get i))=_
      rw [pathRecordsBits_extend,next]
    exact ⟨cost,t,he,⟨by have h:=hh.1;omega,ts,written,
      hh.2.2.2.1.trans (ft.mono Finset.subset_union_right),hh.2.2.2.2.trans tm⟩,
      (ft.tapes 1258 (by decide) (by decide)).trans hw,hc⟩
  have initial : inv e s:=by
    refine ⟨le_rfl,?_,?_,ArchiveFrame.refl _ _,Tree.Memory.Frame.refl _ _ _⟩
    · simpa only [Nat.sub_self,pathOffset_zero] using state
    · simp only [Nat.sub_self,pathRecords_zero,MemoryWord.writeBits]
  obtain ⟨cost,b,finalWord,he,hb,hw,hl,_,hc⟩:=CountedShifted.executes 1258 origin edgeStepCode
    input tape inv (fun _=>edgeStepCost p n) stable body e e.bits s (addressValue_bits e) word initial
  obtain ⟨t,ec,zt,fc⟩:=RuntimeCounter.clear_executes 1258 input tape finalWord origin b hw
  have bs : State data p (packedLength saved) e b:=by
    simpa only [Nat.sub_zero,pathOffset_end] using hb.2.1
  have ts:=bs.control_frame fc.memory (fun j _ hj=>fc.tapes j (by simpa using hj))
    (RationalAccumulator.word_of_eq (fc.tapes 1257 (by decide)) bs.indexWord)
  refine ⟨cost+(6*finalWord.length+4),t,he.seq ec,?_,ts,zt,?_,
    hb.2.2.2.1.trans ((ArchiveFrame.of_binary fc).mono (by decide)),by rw [fc.memory];exact hb.2.2.2.2⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hc
    rw [hl]
    unfold edgeLoopCost
    omega
  · rw [fc.memory]
    simpa only [Nat.sub_zero] using hb.2.2.1

#print axioms edge_loop
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
