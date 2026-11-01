import Maxwell.Continuum.SourceRoutingPathReverseAppend

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryPath GeometryPathPhase Maxwell.Logical.Routing
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
  let cursor₁ := cursor+reverseCount last start₂ (2*q) (2*q)
  let cursor₂ := cursor₁+reverseCount middle start₁ (2*q) (2*q)
  prefixBits p₂ last start₂ (4*q) cursor false (2*q) ++
    prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q) ++
    prefixBits p first start 0 cursor₂ false (2*q)

theorem threePhase_executes {q : ℕ} (p : Plan q)
    (separated₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*q+1) ≤ p.base)
    (first middle last : SortArrays.Keys q) (start : Port q) (cursor n : ℕ)
    (memory : ℕ→Bool)
    (fit₀ : GeometrySort.Fits p.history.width first)
    (fit₁ : GeometrySort.Fits p.history.width middle)
    (fit₂ : GeometrySort.Fits p.history.width last)
    (capacity : cursor+720*q ≤ n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store)
    (state : Runtime ((p.following separated₁).following separated₂) last
      (nextStart middle (nextStart first start)) (4*q) cursor false memory 0 s)
    (counterBlank : Blank s.val 1242)
    (stored₀ : GeometryHistory.Stored p.history first (2*q) s.val.memory)
    (stored₁ : GeometryHistory.Stored p.history.following middle (2*q) s.val.memory) :
    let p₁ := p.following separated₁
    let p₂ := p₁.following separated₂
    let start₁ := nextStart first start
    let start₂ := nextStart middle start₁
    let cursor₁ := cursor+reverseCount last start₂ (2*q) (2*q)
    let cursor₂ := cursor₁+reverseCount middle start₁ (2*q) (2*q)
    let lastBits := prefixBits p₂ last start₂ (4*q) cursor false (2*q)
    let middleBits := prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q)
    ∃steps t,Executes input tape threePhaseCode steps s t ∧
      steps ≤ phaseCost p₂ n+appendCost p₁ n+appendCost p n ∧
      Runtime p first start 0 cursor₂ false
        (MemoryWord.writeBits memory (p.base+cursor*p.width) (lastBits++middleBits)) (2*q) t ∧
      t.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width)
        (threePhaseBits p separated₁ separated₂ first middle last start cursor) ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  dsimp only
  let p₁ := p.following separated₁
  let p₂ := p₁.following separated₂
  let start₁ := nextStart first start
  let start₂ := nextStart middle start₁
  let cursor₁ := cursor+reverseCount last start₂ (2*q) (2*q)
  let cursor₂ := cursor₁+reverseCount middle start₁ (2*q) (2*q)
  let bits₂ := prefixBits p₂ last start₂ (4*q) cursor false (2*q)
  let bits₁ := prefixBits p₁ middle start₁ (2*q) cursor₁ true (2*q)
  obtain ⟨c₀,a,e₀,h₀,r₀,z₀,f₀,m₀⟩ := executes p₂ last start₂ (4*q) cursor n false memory
    fit₂ (by omega) (by omega) input tape s state counterBlank
  have aMemory : a.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width) bits₂ := r₀.written
  obtain ⟨c₁,b,e₁,h₁,r₁,z₁,f₁,m₁⟩ := append_executes p₁ separated₂ middle last start₁
    (2*q) cursor n false memory fit₁ (by omega) (by omega) input tape a
    (by simpa only [show 2*q+2*q=4*q by omega] using r₀) z₀
    (p₁.history_frame middle n stored₁ m₀)
  simp only [Bool.not_false] at r₁
  have bMemory : b.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width) (bits₂++bits₁) := by
    have written := r₁.written
    change b.val.memory=MemoryWord.writeBits a.val.memory (p.base+cursor₁*p.width) bits₁ at written
    rw [aMemory] at written
    have address : p.base+cursor₁*p.width=p.base+cursor*p.width+bits₂.length := by
      dsimp only [cursor₁,bits₂]
      rw [prefixBits_length]
      dsimp only [p₂,p₁,Plan.following]
      ring
    rw [address,writeBits_append] at written
    exact written
  have room : cursor₁+480*q ≤ n := by
    have bounded := reverseCount_bound last start₂ (2*q) (2*q)
    dsimp only [cursor₁]
    omega
  obtain ⟨c₂,t,e₂,h₂,r₂,z₂,f₂,m₂⟩ := append_executes p separated₁ first middle start
    0 cursor₁ n true a.val.memory fit₀ (by omega) room input tape b
    (by simpa only [Nat.zero_add] using r₁) z₁
    (p.history_frame first n stored₀ (m₀.trans m₁))
  have finalState : Runtime p first start 0 cursor₂ false
      (MemoryWord.writeBits memory (p.base+cursor*p.width) (bits₂++bits₁)) (2*q) t := by
    simpa only [Bool.not_true,bMemory] using r₂
  have finalMemory : t.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width)
      (threePhaseBits p separated₁ separated₂ first middle last start cursor) := by
    have written := finalState.written
    have address : p.base+cursor₂*p.width=p.base+cursor*p.width+(bits₂++bits₁).length := by
      simp only [List.length_append,bits₂,bits₁,prefixBits_length]
      dsimp only [cursor₂,cursor₁,p₂,p₁,Plan.following]
      ring
    rw [address,writeBits_append] at written
    exact written
  dsimp only [p₂,p₁] at h₀ h₁
  exact ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),by omega,finalState,finalMemory,z₂,
    f₀.trans (f₁.trans f₂),m₀.trans (m₁.trans m₂)⟩

#print axioms threePhase_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
