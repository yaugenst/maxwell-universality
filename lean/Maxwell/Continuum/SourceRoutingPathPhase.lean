import Maxwell.Continuum.SourceRoutingPathCounter
import Maxwell.Continuum.SourceRoutingPathPhaseLoop
import Maxwell.Cost.Structured.CounterClear

/-! A complete forward phase computes its own traversal count from the stored
grid width, emits every layer, and clears the counter. No prepared counter or
execution trace is supplied by the caller. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def phaseWork : Finset ℕ := GeometryPathCounter.work∪loopWork
def phaseCode (transpose : Bool) : Code :=
  .seq GeometryPathCounter.code (.seq (loopCode transpose) (.call (TapeOps.clear 1242)))
def phaseCost {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  2^32*(p.bound n+3)^2+loopCost p n (2*q).bits.length+6*(2*q).bits.length+4

theorem executes {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor n : ℕ) (transpose : Bool) (memory : ℕ→Bool)
    (fit : GeometrySort.Fits p.history.width initial) (height : level+2*q ≤ 6*q)
    (capacity : cursor+240*q ≤ n) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (state : Runtime p initial start level cursor transpose memory 0 s)
    (counterBlank : Blank s.val 1242) :
    ∃steps t,Executes input tape (phaseCode transpose) steps s t ∧ steps ≤ phaseCost p n ∧
      Runtime p initial start level cursor transpose memory (2*q) t ∧ Blank t.val 1242 ∧
      ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let seed := GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv start).val
  have seedWidth : ∀j∈GeometryArithmetic.ids,(seed j).bits.length ≤ p.bound n := by
    intro j hj
    have h := GeometrySort.seed_width (p.history.layer 0) 1 (finProdFinEquiv start).val
      (finProdFinEquiv start).isLt.le j hj
    have bound := p.history.layer_bound 0 (Nat.zero_le _)
    exact h.trans (bound.trans (by dsimp only [Plan.bound]; omega))
  have countWidth : (2*q).bits.length ≤ p.bound n := by
    have h := Maxwell.Continuum.RationalWords.bits_mono (show 2*q ≤ 6*q+1 by omega)
    dsimp only [Plan.bound]
    omega
  obtain ⟨c0,a,e0,h0,ba,za,pa,ca,f0⟩ := GeometryPathCounter.executes seed q (p.bound n)
    rfl rfl rfl seedWidth countWidth input tape s state.bank state.ready state.privateBlank counterBlank
  have initialState : Runtime p initial start level cursor transpose memory 0 a := by
    refine ⟨state.bound,ba,za,pa,?_,?_,?_,?_,?_,?_⟩
    · exact state.metadata.frame (ArchiveFrame.of_binary f0) (by decide)
    · exact ⟨RationalAccumulator.word_of_eq (f0.tapes 1250 (by decide)) state.output.wordWidth,
        RationalAccumulator.word_of_eq (f0.tapes 1252 (by decide)) state.output.baseWord,
        BankArray.word_of_eq (f0.tapes 1251 (by decide)) state.output.clockWord⟩
    · exact RationalAccumulator.word_of_eq (f0.tapes 1255 (by decide)) state.levelWord
    · exact RationalAccumulator.word_of_eq (f0.tapes 1253 (by decide)) state.cursorWord
    · rw [f0.memory]; exact state.stored
    · exact f0.memory.trans state.written
  obtain ⟨origin,ho⟩ := ca
  obtain ⟨c1,b,word,e1,h1,hb,hw,hl,f1,m1⟩ := loop_executes p initial start level cursor n
    transpose memory fit height capacity input tape (2*q).bits origin (addressValue_bits _)
    a initialState ho
  obtain ⟨t,e2,zt,f2⟩ := RuntimeCounter.clear_executes 1242 input tape word origin b hw
  have finalState := hb.counter_frame f2.memory (fun j hj => f2.tapes j (by simpa using hj))
  refine ⟨c0+(c1+(6*word.length+4)),t,e0.seq (e1.seq e2),?_,finalState,zt,
    ((ArchiveFrame.of_binary f0).mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans
        ((ArchiveFrame.of_binary f2).mono ?_)),?_⟩
  · rw [hl]
    dsimp only [phaseCost]
    omega
  · intro j hj
    have same : j=1242 := by simpa only [Finset.mem_singleton] using hj
    subst j
    simp [loopWork]
  · rw [f2.memory,←f0.memory]
    exact m1

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
