import Maxwell.Continuum.SourceRoutingEmissionState

/-! One original vertex: compute its tile from the enumeration index, emit its
shifted coordinate triple, and advance the actual index word. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2600000
set_option maxRecDepth 16384

def originalStepCode (part : Bool) : Code :=
  .seq originalSelectCode (.seq (originalCode part) (PhysicalEmit.incrementCode 1257))

def originalStepCost {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  2^148*(terminalBound (p.path.history.layer 0) 1 p.path.width p.path.base n+3)^2

theorem original_step {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (p : Plan (2*half)) (vertexRoom : v≤half*half)
    (tile : ∀i,data.tile i=finProdFinEquiv.symm (Fin.castLE vertexRoom i))
    (vertex : Fin v) (part : Bool) (correctPart : data.part vertex=part)
    (cursor n : ℕ) (room : cursor+192≤n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : State data p cursor vertex.val s) :
    ∃steps t,Executes input tape (originalStepCode part) steps s t ∧
      steps≤originalStepCost p n ∧ State data p (cursor+3) (vertex.val+1) t ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
        (pointsBits p.path.width [Gluing.vertexPoint data vertex]) ∧
      ArchiveFrame stepWork s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  obtain ⟨port,bank⟩:=state.bank
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩:=originalSelect_executes (p.path.history.layer 0) 1
    port.val port.isLt.le (Fin.castLE vertexRoom vertex) input tape s bank state.ready state.privateBlank state.indexWord
  have fa : ArchiveFrame stepWork s.val a.val:=(ArchiveFrame.of_binary f₀).mono (by decide)
  have am : Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory a.val.memory:=by
    intro j _;rw [f₀.memory]
  have aa:=state.archive.frame n (fa.mono Finset.subset_union_right) am
  have ba' : NatAssign.Bank ids
      (GeometrySort.seed (p.path.history.layer 0) 1 (finProdFinEquiv (Gluing.tilePort (data.tile vertex) 0)).val) a.val:=by
    rw [tile];exact ba
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,_,_,cb,mb,f₁,m₁⟩:=original_executes data (p.path.history.layer 0) 1
    vertex part correctPart cursor p.path.width p.path.base n p.path.clock p.path.positive p.path.clock_length
    p.path.coordinate_width room input tape a ba' za pa aa.metadata aa.output
    (RationalAccumulator.word_of_eq (f₀.tapes 1253 (by decide)) state.cursorWord)
  have fb : ArchiveFrame stepWork s.val b.val:=fa.trans (f₁.mono (by decide))
  have bmem : Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory b.val.memory:=am.trans m₁
  have bs : State data p (cursor+3) vertex.val b:=by
    refine ⟨⟨finProdFinEquiv (Gluing.tilePort (data.tile vertex) 0),bb⟩,zb,pb,
      state.archive.frame n (fb.mono Finset.subset_union_right) bmem,?_,cb,?_,?_,?_⟩
    · exact RationalAccumulator.word_of_eq
        ((f₁.tapes 1255 (by decide) (by decide)).trans (f₀.tapes 1255 (by decide))) state.levelWord
    · exact RationalAccumulator.word_of_eq
        ((f₁.tapes 1257 (by decide) (by decide)).trans (f₀.tapes 1257 (by decide))) state.indexWord
    · exact RationalAccumulator.blank_of_eq
        ((f₁.tapes 1242 (by decide) (by decide)).trans (f₀.tapes 1242 (by decide))) state.counterBlank
    · exact RationalAccumulator.blank_of_eq
        ((f₁.tapes 1256 (by decide) (by decide)).trans (f₀.tapes 1256 (by decide))) state.savedBlank
  obtain ⟨c₂,t,e₂,h₂,ts,mt,f₂⟩:=bs.increment input tape
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),?_,ts,by rw [mt,mb,f₀.memory],
    fb.trans (f₂.mono (by decide)),by rw [mt];exact bmem⟩
  let B:=terminalBound (p.path.history.layer 0) 1 p.path.width p.path.base n
  have bound : (p.path.history.layer 0).bound 1≤B:=by dsimp [B,terminalBound];omega
  have vb : vertex.val.bits.length≤B:=
    ((Maxwell.Continuum.RationalWords.bits_mono (show vertex.val≤(2*half)*(2*half) by
      have h:=vertex.isLt;nlinarith)).trans ((p.path.history.layer 0).width_bound 1)).trans bound
  have hc₀ : c₀≤2^144*(B+3)^2:=h₀.trans (by gcongr;omega)
  change c₁≤2^142*(B+3)^2 at h₁
  change _≤2^148*(B+3)^2
  nlinarith only [hc₀,h₁,h₂,vb]

#print axioms original_step
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
