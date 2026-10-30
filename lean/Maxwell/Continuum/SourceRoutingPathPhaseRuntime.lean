import Maxwell.Continuum.SourceRoutingPathPhaseMemory

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Runtime {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (memory : ℕ→Bool) (k : ℕ) (s : Store) : Prop where
  bound : k ≤ 2*q
  bank : NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.history.layer k) (k+1)
    (finProdFinEquiv (port initial start k)).val) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  metadata : GeometrySort.Metadata (p.history.layer k) s.val
  output : OutputMetadata p.width p.base p.clock s.val
  levelWord : Word s.val 1255 (level+k)
  cursorWord : Word s.val 1253 (cursor+count initial start k)
  stored : GeometryHistory.Stored p.history initial (2*q) s.val.memory
  written : s.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width) (prefixBits p initial start level cursor transpose k)

theorem Runtime.counter_frame {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {start : Port q}
    {level cursor : ℕ} {transpose : Bool} {memory : ℕ→Bool} {k : ℕ} {s t : Store}
    (state : Runtime p initial start level cursor transpose memory k s) (same : t.val.memory=s.val.memory)
    (keep : ∀j,j≠1242→t.val.tapes j=s.val.tapes j) : Runtime p initial start level cursor transpose memory k t := by
  have word (j : ℕ) (hj : j≠1242) (n : ℕ) (h : Word s.val j n) : Word t.val j n :=
    RationalAccumulator.word_of_eq (keep j hj) h
  refine ⟨state.bound,?_,state.ready.of_tapes (fun j hj => keep j (by omega)),
    RationalAccumulator.blank_of_eq (keep 1249 (by decide)) state.privateBlank,
    ⟨word 711 (by decide) _ state.metadata.width,BankArray.word_of_eq (keep 718 (by decide)) state.metadata.clock⟩,
    ⟨word 1250 (by decide) _ state.output.wordWidth,word 1252 (by decide) _ state.output.baseWord,
      BankArray.word_of_eq (keep 1251 (by decide)) state.output.clockWord⟩,
    word 1255 (by decide) _ state.levelWord,word 1253 (by decide) _ state.cursorWord,
    by rw [same];exact state.stored,same.trans state.written⟩
  intro j hj
  apply word j _ _ (state.bank j hj)
  simp only [GeometryArithmetic.ids,GeometryArithmetic.controls,
    Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hj
  omega

theorem Runtime.counted {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {start : Port q}
    {level cursor : ℕ} {transpose : Bool} {memory : ℕ→Bool} {k : ℕ} {s t : Store}
    (state : Runtime p initial start level cursor transpose memory k s) (frame : CountedShifted.Frame 1242 s t) :
    Runtime p initial start level cursor transpose memory k t :=
  state.counter_frame frame.2.2.1 frame.2.2.2.2.2.1

#print axioms Runtime.counted
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
