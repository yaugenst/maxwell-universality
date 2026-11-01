import Maxwell.Continuum.SourceRoutingPathNetworkMeaning

/-! Fixed forward and reverse routing programs with their physical endpoint,
exact lattice samples, cursor, and saved-memory contracts. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryPathPhase Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def networkForwardCost {q : ℕ} (p : Plan q)
    (sep₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*q+1) ≤ p.base) (n : ℕ) : ℕ :=
  phaseCost p n+appendCost p sep₁ n+appendCost (p.following sep₁) sep₂ n

def networkReverseCost {q : ℕ} (p : Plan q)
    (sep₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*q+1) ≤ p.base) (n : ℕ) : ℕ :=
  GeometryPathReverse.phaseCost ((p.following sep₁).following sep₂) n+
    GeometryPathReverse.appendCost (p.following sep₁) n+GeometryPathReverse.appendCost p n

theorem network_forward {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half))
    (sep₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (incidence : Gluing.Incidence E) (cursor n : ℕ)
    (fits₀ : GeometrySort.Fits p.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.history.width (PhaseKeys.last data.colors))
    (room : cursor+720*(2*half) ≤ n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data incidence)).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (p.history.layer 0) s.val)
    (output : OutputMetadata p.width p.base p.clock s.val)
    (levelWord : Word s.val 1255 0) (cursorWord : Word s.val 1253 cursor) (counterBlank : Blank s.val 1242)
    (stored₀ : GeometryHistory.Stored p.history (PhaseKeys.first data.colors) (2*(2*half)) s.val.memory)
    (stored₁ : GeometryHistory.Stored p.history.following (PhaseKeys.middle data.colors) (2*(2*half)) s.val.memory)
    (stored₂ : GeometryHistory.Stored p.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) s.val.memory) :
    ∃steps t,Executes input tape GeometryPathPhase.threePhaseCode steps s t ∧
      steps ≤ networkForwardCost p sep₁ sep₂ n ∧
      NatAssign.Bank GeometryArithmetic.ids
        (GeometrySort.seed (p.history.following.following.layer (2*(2*half))) (2*(2*half)+1)
          (finProdFinEquiv (Gluing.pairPort (data.pair incidence.1) incidence.2)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      GeometrySort.Metadata (p.history.following.following.layer (2*(2*half))) t.val ∧
      OutputMetadata p.width p.base p.clock t.val ∧ Word t.val 1255 (6*(2*half)) ∧
      Word t.val 1253 (cursor+3*(EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)).length) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width)
        (pointsBits p.width (EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence))) ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  have initial : Runtime p (PhaseKeys.first data.colors) (Gluing.token data incidence) 0 cursor false s.val.memory 0 s :=
    ⟨Nat.zero_le _,bank,ready,privateBlank,metadata,output,levelWord,cursorWord,stored₀,rfl⟩
  obtain ⟨steps,t,he,hc,rt,mem,blank,frame,mframe⟩ := GeometryPathPhase.threePhase_executes p sep₁ sep₂
    (PhaseKeys.first data.colors) (PhaseKeys.middle data.colors) (PhaseKeys.last data.colors)
    (Gluing.token data incidence) cursor n s.val.memory fits₀ fits₁ fits₂ room input tape s initial counterBlank stored₁ stored₂
  have endpoint := (SortPaths.threePhase_target data.colors (Gluing.token data incidence)).trans
    (data.target_incidence incidence.1 incidence.2)
  have count := SortPaths.threePhase_count data.colors (Gluing.token data incidence)
  rw [SortPaths.threePhasePoints_network] at count
  refine ⟨steps,t,he,hc,?_,rt.ready,rt.privateBlank,rt.metadata,rt.output,?_,?_,?_,blank,frame,mframe⟩
  · simpa only [endpoint,Plan.following] using rt.bank
  · convert rt.levelWord using 1; omega
  · convert rt.cursorWord using 1; omega
  · rw [mem,threePhaseBits_network]

theorem network_reverse {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half))
    (sep₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (incidence : Gluing.Incidence E) (cursor n : ℕ)
    (fits₀ : GeometrySort.Fits p.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.history.width (PhaseKeys.last data.colors))
    (room : cursor+720*(2*half) ≤ n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.following.following.layer (2*(2*half))) (2*(2*half)+1)
        (finProdFinEquiv (Gluing.pairPort (data.pair incidence.1) incidence.2)).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (p.history.following.following.layer (2*(2*half))) s.val)
    (output : OutputMetadata p.width p.base p.clock s.val)
    (levelWord : Word s.val 1255 (6*(2*half))) (cursorWord : Word s.val 1253 cursor) (counterBlank : Blank s.val 1242)
    (stored₀ : GeometryHistory.Stored p.history (PhaseKeys.first data.colors) (2*(2*half)) s.val.memory)
    (stored₁ : GeometryHistory.Stored p.history.following (PhaseKeys.middle data.colors) (2*(2*half)) s.val.memory)
    (stored₂ : GeometryHistory.Stored p.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) s.val.memory) :
    ∃steps t,Executes input tape GeometryPathReverse.threePhaseCode steps s t ∧
      steps ≤ networkReverseCost p sep₁ sep₂ n ∧
      NatAssign.Bank GeometryArithmetic.ids
        (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data incidence)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (p.history.layer 0) t.val ∧
      OutputMetadata p.width p.base p.clock t.val ∧ Word t.val 1255 0 ∧
      Word t.val 1253 (cursor+3*(EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)).length) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width)
        (pointsBits p.width ((EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)).reverse)) ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  have endpoint := (SortPaths.threePhase_target data.colors (Gluing.token data incidence)).trans
    (data.target_incidence incidence.1 incidence.2)
  have initial : GeometryPathReverse.Runtime ((p.following sep₁).following sep₂) (PhaseKeys.last data.colors)
      (nextStart (PhaseKeys.middle data.colors) (nextStart (PhaseKeys.first data.colors) (Gluing.token data incidence)))
      (4*(2*half)) cursor false s.val.memory 0 s := by
    refine ⟨Nat.zero_le _,?_,ready,privateBlank,metadata,output,?_,cursorWord,stored₂,rfl⟩
    · simpa only [Nat.sub_zero,Plan.following,endpoint] using bank
    · convert levelWord using 1; omega
  obtain ⟨steps,t,he,hc,rt,mem,blank,frame,mframe⟩ := GeometryPathReverse.threePhase_executes p sep₁ sep₂
    (PhaseKeys.first data.colors) (PhaseKeys.middle data.colors) (PhaseKeys.last data.colors)
    (Gluing.token data incidence) cursor n s.val.memory fits₀ fits₁ fits₂ room input tape s initial counterBlank stored₀ stored₁
  have count := SortPaths.threePhase_count data.colors (Gluing.token data incidence)
  rw [SortPaths.threePhasePoints_network] at count
  have cursorEnd := rt.cursorWord
  simp only [SortPaths.reverseCount_end] at cursorEnd
  refine ⟨steps,t,he,hc,?_,rt.ready,rt.privateBlank,?_,rt.output,?_,?_,?_,blank,frame,mframe⟩
  · simpa only [Nat.sub_self,Nat.zero_add,SortPaths.port] using rt.bank
  · simpa only [Nat.sub_self] using rt.metadata
  · simpa only [Nat.sub_self,Nat.add_zero] using rt.levelWord
  · convert cursorEnd using 1; omega
  · rw [mem,reverseThreePhaseBits_network]

#print axioms network_forward
#print axioms network_reverse
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
