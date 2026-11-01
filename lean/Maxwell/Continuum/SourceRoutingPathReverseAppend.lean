import Maxwell.Continuum.SourceRoutingPathReversePhase
import Maxwell.Continuum.SourceRoutingPathReverseRestart
import Maxwell.Continuum.SourceRoutingPathAppend

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryPath GeometryPathPhase Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def appendCode (transpose : Bool) : Code :=
  .seq restartCode (.seq transposePort.code (phaseCode (!transpose)))

def appendCost {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  restartCost p.history+2^128*((p.history.layer (2*q)).bound (2*q+1)+2)^2+phaseCost p n

theorem append_executes {q : ℕ} (p : Plan q)
    (separated : p.history.following.slab (2*q+1) ≤ p.base)
    (lower upper : SortArrays.Keys q) (start : Port q)
    (level cursor n : ℕ) (transpose : Bool) (memory : ℕ→Bool)
    (fit : GeometrySort.Fits p.history.width lower) (height : level+2*q ≤ 6*q)
    (capacity : cursor+480*q ≤ n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : Runtime (p.following separated) upper (nextStart lower start)
      (level+2*q) cursor transpose memory (2*q) s)
    (counterBlank : Blank s.val 1242)
    (stored : GeometryHistory.Stored p.history lower (2*q) s.val.memory) :
    ∃steps t,Executes input tape (appendCode transpose) steps s t ∧ steps ≤ appendCost p n ∧
      Runtime p lower start level
        (cursor+reverseCount upper (nextStart lower start) (2*q) (2*q)) (!transpose) s.val.memory (2*q) t ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let current := nextStart lower start
  have currentBank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.following.layer 0) 1 (finProdFinEquiv current).val) s.val := by
    simpa only [Nat.sub_self,Nat.zero_add,port,Plan.following,current] using state.bank
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩ := restart_executes p.history (finProdFinEquiv current).val
    (finProdFinEquiv current).isLt.le input tape s currentBank state.ready state.privateBlank
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,f₁⟩ := transposePort_executes
    (p.history.layer (2*q)) (2*q+1) current input tape a ba za pa
  have frame := f₀.trans f₁
  have initialState : Runtime p lower start level
      (cursor+reverseCount upper (nextStart lower start) (2*q) (2*q)) (!transpose) s.val.memory 0 b := by
    refine ⟨Nat.zero_le _,?_,zb,pb,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.sub_zero,current,SortPaths.nextStart,Prod.swap] using bb
    · have metadata := state.metadata.frame (ArchiveFrame.of_binary frame) (by decide)
      exact ⟨metadata.width,metadata.clock⟩
    · exact ⟨RationalAccumulator.word_of_eq (frame.tapes 1250 (by decide)) state.output.wordWidth,
        RationalAccumulator.word_of_eq (frame.tapes 1252 (by decide)) state.output.baseWord,
        BankArray.word_of_eq (frame.tapes 1251 (by decide)) state.output.clockWord⟩
    · simpa only [Nat.sub_self,Nat.sub_zero,Nat.add_zero] using
        RationalAccumulator.word_of_eq (frame.tapes 1255 (by decide)) state.levelWord
    · simpa only [reverseCount,Nat.add_zero] using
        RationalAccumulator.word_of_eq (frame.tapes 1253 (by decide)) state.cursorWord
    · rw [frame.memory];exact stored
    · simpa only [prefixBits,MemoryWord.writeBits] using frame.memory
  have room : cursor+reverseCount upper (nextStart lower start) (2*q) (2*q)+240*q ≤ n := by
    have bounded := reverseCount_bound upper (nextStart lower start) (2*q) (2*q)
    omega
  obtain ⟨c₂,t,e₂,h₂,rt,zt,f₂,m₂⟩ := executes p lower start level
    (cursor+reverseCount upper (nextStart lower start) (2*q) (2*q)) n (!transpose) s.val.memory
    fit height room input tape b initialState
    (RationalAccumulator.blank_of_eq (frame.tapes 1242 (by decide)) counterBlank)
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),?_,rt,zt,
    ((ArchiveFrame.of_binary frame).mono ?_).trans f₂,?_⟩
  · dsimp only [appendCost];omega
  · intro j hj
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)
  · simpa only [frame.memory] using m₂

#print axioms append_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
