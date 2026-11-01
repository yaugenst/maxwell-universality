import Maxwell.Continuum.SourceRoutingEmissionState

/-! One packed path selected by its active-edge index. The body preserves the
outer countdown and retains all routing history and source inverse entries. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2600000
set_option maxRecDepth 16384

def edgeStepCode : Code :=
  .seq edgeSelectCode (.seq packedEdgeCode (PhysicalEmit.incrementCode 1257))

def edgeStepCost {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  edgeCost p.path p.secondBefore p.thirdBefore n+
    2^130*(edgeSelectBound (p.path.history.layer 0) 1 p.backward+3)^2+
    2^120*(terminalBound (p.path.history.layer 0) 1 p.path.width p.path.base n+3)^2

theorem edge_step {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (p : Plan (2*half)) (edgeRoom : e≤half*(2*half))
    (pair : ∀i,data.pair i=finProdFinEquiv.symm (Fin.castLE edgeRoom i))
    (edge : Fin e) (cursor n : ℕ)
    (fits₀ : GeometrySort.Fits p.path.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.path.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.path.history.width (PhaseKeys.last data.colors))
    (room : cursor+1+3072*(2*half)≤n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : State data p cursor edge.val s) :
    ∃steps t,Executes input tape edgeStepCode steps s t ∧
      steps≤edgeStepCost p n ∧
      State data p (cursor+1+3*(EdgeEmission.edge data (EdgeEmission.prepare data) edge).length) (edge.val+1) t ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.path.base+cursor*p.path.width)
        (packedEdgeBits p.path.width (EdgeEmission.edge data (EdgeEmission.prepare data) edge)) ∧
      ArchiveFrame stepWork s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  obtain ⟨port,bank⟩:=state.bank
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,_,ma,f₀⟩:=edgeSelect_executes data (p.path.history.layer 0) 1
    port.val p.backward port.isLt.le edge (Fin.castLE edgeRoom edge) (pair edge) input tape s bank
    state.ready state.privateBlank state.archive.metadata state.indexWord state.archive.backwardWord
    state.archive.backwardStored
  have fa : ArchiveFrame stepWork s.val a.val:=f₀.mono (by decide)
  have am : Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory a.val.memory:=by
    intro j _;rw [ma]
  have aa:=state.archive.frame n (fa.mono Finset.subset_union_right) am
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,_,_,lb,cb,mb,kb,sb,f₁,m₁⟩:=packedEdge_executes data p.path
    p.secondBefore p.thirdBefore edge cursor n fits₀ fits₁ fits₂ room input tape a ba za pa aa.metadata aa.output
    (RationalAccumulator.word_of_eq (f₀.tapes 1255 (by decide) (by decide)) state.levelWord)
    (RationalAccumulator.word_of_eq (f₀.tapes 1253 (by decide) (by decide)) state.cursorWord)
    (RationalAccumulator.blank_of_eq (f₀.tapes 1242 (by decide) (by decide)) state.counterBlank)
    (RationalAccumulator.blank_of_eq (f₀.tapes 1256 (by decide) (by decide)) state.savedBlank)
    aa.first aa.second aa.third
  have fb : ArchiveFrame stepWork s.val b.val:=fa.trans (f₁.mono Finset.subset_union_right)
  have bmem:=am.trans m₁
  have bs : State data p (cursor+1+3*(EdgeEmission.edge data (EdgeEmission.prepare data) edge).length) edge.val b:=
    ⟨⟨finProdFinEquiv (Gluing.token data (edge,true)),bb⟩,zb,pb,
      state.archive.frame n (fb.mono Finset.subset_union_right) bmem,lb,cb,
      RationalAccumulator.word_of_eq
        ((f₁.tapes 1257 (by decide) (by decide)).trans (f₀.tapes 1257 (by decide) (by decide))) state.indexWord,kb,sb⟩
  obtain ⟨c₂,t,e₂,h₂,ts,mt,f₂⟩:=bs.increment input tape
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),?_,ts,by rw [mt,mb,ma],
    fb.trans (f₂.mono (by decide)),by rw [mt];exact bmem⟩
  let B:=edgeSelectBound (p.path.history.layer 0) 1 p.backward
  have bound : (p.path.history.layer 0).bound 1≤B:=by dsimp [B,edgeSelectBound];omega
  have eb : edge.val.bits.length≤B:=
    ((Maxwell.Continuum.RationalWords.bits_mono (show edge.val≤(2*half)*(2*half) by
      have h:=edge.isLt;nlinarith)).trans ((p.path.history.layer 0).width_bound 1)).trans bound
  unfold edgeStepCost
  change c₀≤2^126*(B+3)^2 at h₀
  nlinarith only [h₀,h₁,h₂,eb]

#print axioms edge_step
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
