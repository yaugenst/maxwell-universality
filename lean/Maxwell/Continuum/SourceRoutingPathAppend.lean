import Maxwell.Continuum.SourceRoutingPathPhase
import Maxwell.Logical.Routing.SortPathsThreePhase
import Maxwell.Continuum.SourceRoutingPathTranspose
import Maxwell.Continuum.SourceRoutingHistoryRestart

/-! Continue a path into the next stored history: update the history addresses,
transpose the port, then execute the complete next phase. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def Plan.following {q : ℕ} (p : Plan q)
    (separated : p.history.following.slab (2*q+1) ≤ p.base) : Plan q where
  history := p.history.following
  base := p.base
  width := p.width
  clock := p.clock
  positive := p.positive
  clock_length := p.clock_length
  coordinate_width := p.coordinate_width
  separated := separated

export Maxwell.Logical.Routing.SortPaths (nextStart)

def appendCode (transpose : Bool) : Code :=
  .seq (NatAssign.code GeometryHistory.restart)
    (.seq transposePort.code (phaseCode (!transpose)))

def appendCost {q : ℕ} (p : Plan q)
    (separated : p.history.following.slab (2*q+1) ≤ p.base) (n : ℕ) : ℕ :=
  2^40*(p.history.bound+3)^2+
    2^128*((p.history.following.layer 0).bound 1+2)^2+
    phaseCost (p.following separated) n

theorem append_executes {q : ℕ} (p : Plan q)
    (separated : p.history.following.slab (2*q+1) ≤ p.base)
    (initial next : SortArrays.Keys q) (start : Port q)
    (level cursor n : ℕ) (transpose : Bool) (memory : ℕ→Bool)
    (fit : GeometrySort.Fits p.history.width next) (height : level+4*q ≤ 6*q)
    (capacity : cursor+480*q ≤ n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : Runtime p initial start level cursor transpose memory (2*q) s)
    (counterBlank : Blank s.val 1242)
    (stored : GeometryHistory.Stored p.history.following next (2*q) s.val.memory) :
    ∃steps t,Executes input tape (appendCode transpose) steps s t ∧ steps ≤ appendCost p separated n ∧
      Runtime (p.following separated) next (nextStart initial start) (level+2*q)
        (cursor+count initial start (2*q)) (!transpose) s.val.memory (2*q) t ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let current := port initial start (2*q)
  obtain ⟨c0,a,e0,h0,ba,za,pa,f0⟩ := GeometryHistory.restart_executes p.history
    (finProdFinEquiv current).val (finProdFinEquiv current).isLt.le input tape s
    state.bank state.ready state.privateBlank
  obtain ⟨c1,b,e1,h1,bb,zb,pb,f1⟩ := transposePort_executes
    (p.history.following.layer 0) 1 current input tape a ba za pa
  have frame := f0.trans f1
  have initialState : Runtime (p.following separated) next (nextStart initial start) (level+2*q)
      (cursor+count initial start (2*q)) (!transpose) s.val.memory 0 b := by
    refine ⟨Nat.zero_le _,bb,zb,pb,?_,?_,?_,?_,?_,?_⟩
    · have metadata := state.metadata.frame (ArchiveFrame.of_binary frame) (by decide)
      exact ⟨metadata.width, metadata.clock⟩
    · exact ⟨RationalAccumulator.word_of_eq (frame.tapes 1250 (by decide)) state.output.wordWidth,
        RationalAccumulator.word_of_eq (frame.tapes 1252 (by decide)) state.output.baseWord,
        BankArray.word_of_eq (frame.tapes 1251 (by decide)) state.output.clockWord⟩
    · simpa only [Nat.add_zero] using
        RationalAccumulator.word_of_eq (frame.tapes 1255 (by decide)) state.levelWord
    · simpa only [count,Nat.add_zero] using
        RationalAccumulator.word_of_eq (frame.tapes 1253 (by decide)) state.cursorWord
    · rw [frame.memory]; exact stored
    · simpa only [prefixBits,MemoryWord.writeBits] using frame.memory
  have room : cursor+count initial start (2*q)+240*q ≤ n := by
    have bounded := count_bound initial start (2*q)
    omega
  obtain ⟨c2,t,e2,h2,rt,zt,f2,m2⟩ := executes (p.following separated) next (nextStart initial start)
    (level+2*q) (cursor+count initial start (2*q)) n (!transpose) s.val.memory fit
    (by omega) room input tape b initialState
    (RationalAccumulator.blank_of_eq (frame.tapes 1242 (by decide)) counterBlank)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,rt,zt,
    ((ArchiveFrame.of_binary frame).mono ?_).trans f2,?_⟩
  · dsimp only [appendCost]; omega
  · intro j hj
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)
  · simpa only [frame.memory,Plan.following] using m2

#print axioms append_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
