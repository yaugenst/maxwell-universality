import Maxwell.Continuum.SourceRoutingPathAppend

/-! Execute the complete row-column-row path from three stored histories.
The output equation records the actual concatenated geometry words in memory. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def threePhaseCode : Code :=
  .seq (phaseCode false) (.seq (appendCode false) (appendCode true))

def threePhaseBits {q : ℕ} (p : Plan q)
    (separated₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*q+1) ≤ p.base)
    (first middle last : SortArrays.Keys q) (start : Port q) (cursor : ℕ) : List Bool :=
  let p₁ := p.following separated₁
  let p₂ := p₁.following separated₂
  let start₁ := nextStart first start
  let start₂ := nextStart middle start₁
  let cursor₁ := cursor+count first start (2*q)
  let cursor₂ := cursor₁+count middle start₁ (2*q)
  prefixBits p first start 0 cursor false (2*q) ++
    prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q) ++
    prefixBits p₂ last start₂ (4*q) cursor₂ false (2*q)

theorem threePhase_executes {q : ℕ} (p : Plan q)
    (separated₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*q+1) ≤ p.base)
    (first middle last : SortArrays.Keys q) (start : Port q) (cursor n : ℕ)
    (memory : ℕ→Bool)
    (fit₀ : GeometrySort.Fits p.history.width first)
    (fit₁ : GeometrySort.Fits p.history.width middle)
    (fit₂ : GeometrySort.Fits p.history.width last)
    (capacity : cursor+720*q ≤ n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : Runtime p first start 0 cursor false memory 0 s)
    (counterBlank : Blank s.val 1242)
    (stored₁ : GeometryHistory.Stored p.history.following middle (2*q) s.val.memory)
    (stored₂ : GeometryHistory.Stored p.history.following.following last (2*q) s.val.memory) :
    let p₁ := p.following separated₁
    let p₂ := p₁.following separated₂
    let start₁ := nextStart first start
    let start₂ := nextStart middle start₁
    let cursor₁ := cursor+count first start (2*q)
    let cursor₂ := cursor₁+count middle start₁ (2*q)
    let firstBits := prefixBits p first start 0 cursor false (2*q)
    let middleBits := prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q)
    ∃steps t, Executes input tape threePhaseCode steps s t ∧
      steps ≤ phaseCost p n+appendCost p separated₁ n+appendCost p₁ separated₂ n ∧
      Runtime p₂ last start₂ (4*q) cursor₂ false
        (MemoryWord.writeBits memory (p.base+cursor*p.width) (firstBits++middleBits)) (2*q) t ∧
      t.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width)
        (threePhaseBits p separated₁ separated₂ first middle last start cursor) ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  dsimp only
  let p₁ := p.following separated₁
  let p₂ := p₁.following separated₂
  let start₁ := nextStart first start
  let start₂ := nextStart middle start₁
  let cursor₁ := cursor+count first start (2*q)
  let cursor₂ := cursor₁+count middle start₁ (2*q)
  let bits₀ := prefixBits p first start 0 cursor false (2*q)
  let bits₁ := prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q)
  obtain ⟨c₀,a,e₀,h₀,r₀,z₀,f₀,m₀⟩ := executes p first start 0 cursor n false memory
    fit₀ (by omega) (by omega) input tape s state counterBlank
  have aMemory : a.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width) bits₀ := r₀.written
  obtain ⟨c₁,b,e₁,h₁,r₁,z₁,f₁,m₁⟩ := append_executes p separated₁ first middle start
    0 cursor n false memory fit₁ (by omega) (by omega) input tape a r₀ z₀
    (p₁.history_frame middle n stored₁ m₀)
  simp only [Nat.zero_add,Bool.not_false] at r₁
  have bMemory : b.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width) (bits₀++bits₁) := by
    have written := r₁.written
    change b.val.memory=MemoryWord.writeBits a.val.memory (p.base+cursor₁*p.width) bits₁ at written
    rw [aMemory] at written
    have address : p.base+cursor₁*p.width=p.base+cursor*p.width+bits₀.length := by
      dsimp only [cursor₁,bits₀]
      rw [prefixBits_length]
      ring
    rw [address,writeBits_append] at written
    exact written
  have room : cursor₁+480*q ≤ n := by
    have bounded := count_bound first start (2*q)
    dsimp only [cursor₁]
    omega
  obtain ⟨c₂,t,e₂,h₂,r₂,z₂,f₂,m₂⟩ := append_executes p₁ separated₂ middle last start₁
    (2*q) cursor₁ n true a.val.memory fit₂ (by omega) room input tape b r₁ z₁
    (p₂.history_frame last n stored₂ (m₀.trans m₁))
  have finalState : Runtime p₂ last start₂ (4*q) cursor₂ false
      (MemoryWord.writeBits memory (p.base+cursor*p.width) (bits₀++bits₁)) (2*q) t := by
    have level : 2*q+2*q=4*q := by omega
    simpa only [Bool.not_true,level,bMemory] using r₂
  have finalMemory : t.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width)
      (threePhaseBits p separated₁ separated₂ first middle last start cursor) := by
    have written := finalState.written
    have address : p₂.base+cursor₂*p₂.width=p.base+cursor*p.width+(bits₀++bits₁).length := by
      simp only [List.length_append,bits₀,bits₁,prefixBits_length]
      dsimp only [cursor₂,cursor₁,p₂,p₁,Plan.following]
      ring
    rw [address,writeBits_append] at written
    exact written
  dsimp only [p₁] at h₂
  exact ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),by omega,finalState,finalMemory,z₂,
    f₀.trans (f₁.trans f₂),m₀.trans (m₁.trans m₂)⟩

#print axioms threePhase_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
