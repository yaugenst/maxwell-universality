import Maxwell.Continuum.SourceRoutingPathReverseStep
import Maxwell.Continuum.SourceRoutingPathPhaseRuntime
import Maxwell.Logical.Routing.SortPathsReverse

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryPath Maxwell.Logical.Routing GeometryPathPhase
open RationalAccumulator (Word Blank)
export Maxwell.Logical.Routing.SortPaths (reverseCount reverseCount_bound)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def prefixBits {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) : ℕ→List Bool
  | 0 => []
  | k+1 => prefixBits p initial start level cursor transpose k++
      emittedBits (p.history.layer (2*q-(k+1))) (2*q-(k+1)+1)
        (SortArrays.run initial (2*q-(k+1))) (finProdFinEquiv (port initial start (2*q-(k+1))))
        (level+(2*q-(k+1))) (cursor+reverseCount initial start (2*q) k) p.width transpose true

theorem prefixBits_length {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) :
    (prefixBits p initial start level cursor transpose k).length=reverseCount initial start (2*q) k*p.width := by
  induction k with
  | zero => simp [prefixBits,reverseCount]
  | succ k ih =>
    rw [prefixBits,List.length_append,ih,emittedBits_length (backwards := true),Equiv.symm_apply_apply]
    change reverseCount initial start (2*q) k*p.width+3*length initial start (2*q-(k+1))*p.width=
      (reverseCount initial start (2*q) k+3*length initial start (2*q-(k+1)))*p.width
    ring

structure Runtime {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (memory : ℕ→Bool) (k : ℕ) (s : Store) : Prop where
  bound : k ≤ 2*q
  bank : NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.history.layer (2*q-k)) (2*q-k+1)
    (finProdFinEquiv (port initial start (2*q-k))).val) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  metadata : GeometrySort.Metadata (p.history.layer (2*q-k)) s.val
  output : OutputMetadata p.width p.base p.clock s.val
  levelWord : Word s.val 1255 (level+(2*q-k))
  cursorWord : Word s.val 1253 (cursor+reverseCount initial start (2*q) k)
  stored : GeometryHistory.Stored p.history initial (2*q) s.val.memory
  written : s.val.memory=MemoryWord.writeBits memory (p.base+cursor*p.width)
    (prefixBits p initial start level cursor transpose k)

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

theorem prefix_extend {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) (memory : ℕ→Bool) :
    MemoryWord.writeBits (MemoryWord.writeBits memory (p.base+cursor*p.width)
      (prefixBits p initial start level cursor transpose k))
      (p.base+(cursor+reverseCount initial start (2*q) k)*p.width)
      (emittedBits (p.history.layer (2*q-(k+1))) (2*q-(k+1)+1)
        (SortArrays.run initial (2*q-(k+1))) (finProdFinEquiv (port initial start (2*q-(k+1))))
        (level+(2*q-(k+1))) (cursor+reverseCount initial start (2*q) k) p.width transpose true)=
    MemoryWord.writeBits memory (p.base+cursor*p.width) (prefixBits p initial start level cursor transpose (k+1)) := by
  have address : p.base+(cursor+reverseCount initial start (2*q) k)*p.width=
      p.base+cursor*p.width+(prefixBits p initial start level cursor transpose k).length := by
    rw [prefixBits_length]
    ring
  rw [address,writeBits_append]
  rfl

#print axioms Runtime.counted
#print axioms prefix_extend
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
