import Maxwell.Continuum.SourceRoutingEdge
import Maxwell.Continuum.SourceRoutingPathReserve
import Maxwell.Continuum.SourceRoutingPathHeader
import Maxwell.Cost.MemoryWord.Backpatch

/-! Each active edge is traversed once. Its reserved count is filled from the
actual cursor difference, producing the packed geometry serializer format. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryPathPhase Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 3200000

def packedEdgeCode : Code := .seq reserveCode (.seq edgeCode headerCode)
def packedEdgeWork : Finset ℕ := {1256}∪phaseWork
def packedEdgeBits (width : ℕ) (points : List Point) : List Bool :=
  IncidenceEncoding.word width points.length++pointsBits width points

theorem edge_words_bound {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (positive : 0<2*half) (edge : E) :
    3*(EdgeEmission.edge data (EdgeEmission.prepare data) edge).length ≤ 3072*(2*half) := by
  have a:=bottom_words_bound data (edge,false)
  have b:=network_words_bound data (edge,false)
  have c:=network_words_bound data (edge,true)
  have d:=bottom_words_bound data (edge,true)
  rw [edge_parts]
  simp only [List.length_append,List.length_singleton,List.length_reverse,top_prefix_length]
  omega

theorem packedEdgeBits_length (width : ℕ) (points : List Point) :
    (packedEdgeBits width points).length=(1+3*points.length)*width := by
  simp only [packedEdgeBits,List.length_append,IncidenceEncoding.word_length,pointsBits_length]
  ring

theorem packedEdge_executes {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half))
    (sep₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (edge : E) (cursor n : ℕ)
    (fits₀ : GeometrySort.Fits p.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.history.width (PhaseKeys.last data.colors))
    (room : cursor+1+3072*(2*half) ≤ n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data (edge,false))).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (p.history.layer 0) s.val)
    (output : OutputMetadata p.width p.base p.clock s.val)
    (levelWord : Word s.val 1255 0) (cursorWord : Word s.val 1253 cursor)
    (counterBlank : Blank s.val 1242) (savedBlank : Blank s.val 1256)
    (stored₀ : GeometryHistory.Stored p.history (PhaseKeys.first data.colors) (2*(2*half)) s.val.memory)
    (stored₁ : GeometryHistory.Stored p.history.following (PhaseKeys.middle data.colors) (2*(2*half)) s.val.memory)
    (stored₂ : GeometryHistory.Stored p.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) s.val.memory) :
    ∃steps t,Executes input tape packedEdgeCode steps s t ∧
      steps ≤ edgeCost p sep₁ sep₂ n+2^118*(terminalBound (p.history.layer 0) 1 p.width p.base n+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids
        (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data (edge,true))).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (p.history.layer 0) t.val ∧
      OutputMetadata p.width p.base p.clock t.val ∧ Word t.val 1255 0 ∧
      Word t.val 1253 (cursor+1+3*(EdgeEmission.edge data (EdgeEmission.prepare data) edge).length) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width)
        (packedEdgeBits p.width (EdgeEmission.edge data (EdgeEmission.prepare data) edge)) ∧
      Blank t.val 1242 ∧ Blank t.val 1256 ∧ ArchiveFrame packedEdgeWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let points:=EdgeEmission.edge data (EdgeEmission.prepare data) edge
  let B:=terminalBound (p.history.layer 0) 1 p.width p.base n
  have pb : (p.history.layer 0).bound 1 ≤ B:=by dsimp [B,terminalBound];omega
  have nb : n.bits.length ≤ B:=by dsimp [B,terminalBound];omega
  have cb : cursor.bits.length ≤ B:=
    (Maxwell.Continuum.RationalWords.bits_mono (by omega : cursor ≤ n)).trans nb
  have lengthBound:=edge_words_bound data p.history.positive edge
  have nextBound : (cursor+1+3*points.length).bits.length ≤ B:=
    (Maxwell.Continuum.RationalWords.bits_mono (by dsimp only [points];omega : cursor+1+3*points.length ≤ n)).trans nb
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,ca,sa,f₀⟩:=reserve_executes (p.history.layer 0) 1
    (finProdFinEquiv (Gluing.token data (edge,false))).val cursor B
    (finProdFinEquiv (Gluing.token data (edge,false))).isLt.le pb cb input tape s bank ready privateBlank cursorWord savedBlank
  have ma:=metadata.frame (ArchiveFrame.of_binary f₀) (by decide)
  have oa : OutputMetadata p.width p.base p.clock a.val:=
    ⟨RationalAccumulator.word_of_eq (f₀.tapes 1250 (by decide)) output.wordWidth,
      RationalAccumulator.word_of_eq (f₀.tapes 1252 (by decide)) output.baseWord,
      BankArray.word_of_eq (f₀.tapes 1251 (by decide)) output.clockWord⟩
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pbBlank,mb,ob,lb,cbWord,memB,kb,f₁,m₁⟩:=edge_executes data p sep₁ sep₂ edge
    (cursor+1) n fits₀ fits₁ fits₂ room input tape a ba za pa ma oa
    (RationalAccumulator.word_of_eq (f₀.tapes 1255 (by decide)) levelWord) ca
    (RationalAccumulator.blank_of_eq (f₀.tapes 1242 (by decide)) counterBlank)
    (by rw [f₀.memory];exact stored₀) (by rw [f₀.memory];exact stored₁) (by rw [f₀.memory];exact stored₂)
  obtain ⟨c₂,t,e₂,h₂,bt,zt,pt,ot,st,memT,f₂,m₂⟩:=header_executes (p.history.layer 0) 1
    (finProdFinEquiv (Gluing.token data (edge,true))).val
    (finProdFinEquiv (Gluing.token data (edge,true))).isLt.le cursor points.length p.width p.base n B p.clock
    (by dsimp [B,terminalBound];omega) pb (by dsimp [B,terminalBound];omega)
    (by dsimp [B,terminalBound];omega) nextBound p.positive p.clock_length
    ((Maxwell.Continuum.RationalWords.bits_mono (EdgeEmission.edge_length_le data edge)).trans p.coordinate_width)
    (by omega) input tape b bb zb pbBlank ob
    (RationalAccumulator.word_of_eq (f₁.tapes 1256 (by decide) (by decide)) sa) cbWord
  have written : t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width)
      (packedEdgeBits p.width points) := by
    rw [memT,memB,f₀.memory]
    have address : p.base+(cursor+1)*p.width=p.base+cursor*p.width+
        (IncidenceEncoding.word p.width points.length).length := by
      rw [IncidenceEncoding.word_length];ring
    rw [address,MemoryWord.writeBits_prepend]
    rfl
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),?_,bt,zt,pt,mb.frame f₂ (by decide),ot,
    RationalAccumulator.word_of_eq (f₂.tapes 1255 (by decide) (by decide)) lb,
    RationalAccumulator.word_of_eq (f₂.tapes 1253 (by decide) (by decide)) cbWord,written,
    RationalAccumulator.blank_of_eq (f₂.tapes 1242 (by decide) (by decide)) kb,st,
    ((ArchiveFrame.of_binary f₀).mono (by decide)).trans
      ((f₁.mono Finset.subset_union_right).trans (f₂.mono (by decide))),?_⟩
  · dsimp only [B] at h₀ h₂
    omega
  · rw [f₀.memory] at m₁
    exact m₁.trans m₂

#print axioms packedEdge_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
