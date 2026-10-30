import Maxwell.Continuum.SourceRoutingSplitReusable
import Maxwell.Continuum.WordCleanup
import Maxwell.Cost.RoutingAllocator

/-! Every live split-node word has an explicit represented payload.
One fixed scan list clears all node metadata for the next iteration. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.NodeCleanup
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure State (layout : SplitNode.Layout) (k : ℕ) (clock childClock : List Bool)
    (header : ℕ→ℕ) (s : BitRAMState) : Prop where
  child : ChildPermutation.Config (layout.child (2*2^k)) [] clock childClock s
  route : DoublingPass.Config (BinarySplit.finalLayout layout.split (2*2^k)) [] clock s
  saved : BinarySplit.Saved layout.split s
  workspace : DoublingInit.Workspace s
  zero94 : Blank s 94
  zero95 : Blank s 95
  zero97 : Blank s 97
  zero126 : Blank s 126
  count : Word s 96 (2*2^k).bits
  childCount : Word s 127 (2^k).bits
  inputA : Word s 98 layout.split.half.inputA.bits
  inputB : Word s 99 layout.split.half.inputB.bits
  header : ∀i∈Finset.Icc 190 196,RationalAccumulator.Word s i (header i)

def entries (layout : SplitNode.Layout) (k : ℕ) (clock childClock : List Bool)
    (header : ℕ→ℕ) : List (ℕ×List Bool) := [
  (80,layout.split.route.width.bits),
  (81,[]),
  (82,(BinarySplit.finalLayout layout.split (2*2^k)).oldJump.bits),
  (83,clock),
  (84,(BinarySplit.finalLayout layout.split (2*2^k)).oldMinimum.bits),
  (85,(BinarySplit.finalLayout layout.split (2*2^k)).newJump.bits),
  (86,[true]),
  (87,[false]),
  (88,[]),
  (89,[]),
  (90,[]),
  (91,[]),
  (92,[]),
  (94,[]),
  (95,[]),
  (96,(2*2^k).bits),
  (97,[]),
  (98,layout.split.half.inputA.bits),
  (99,layout.split.half.inputB.bits),
  (100,layout.split.forward.bits),
  (101,layout.split.backward.bits),
  (102,layout.split.route.oldJump.bits),
  (103,layout.split.route.oldMinimum.bits),
  (104,layout.split.route.newJump.bits),
  (105,layout.split.route.newMinimum.bits),
  (120,(layout.child (2*2^k)).childWidth.bits),
  (121,childClock),
  (122,((layout.child (2*2^k)).outputBase 0).bits),
  (123,((layout.child (2*2^k)).outputBase 1).bits),
  (124,((layout.child (2*2^k)).outputBase 2).bits),
  (125,((layout.child (2*2^k)).outputBase 3).bits),
  (126,[]),
  (127,(2^k).bits),
  (128,(layout.child (2*2^k)).colors.bits),
  (190,(header 190).bits),
  (191,(header 191).bits),
  (192,(header 192).bits),
  (193,(header 193).bits),
  (194,(header 194).bits),
  (195,(header 195).bits),
  (196,(header 196).bits)]

def banks : List ℕ := [80,81,82,83,84,85,86,87,88,89,90,91,92,94,95,96,97,98,99,100,101,102,103,104,105,120,121,122,123,124,125,126,127,128,190,191,192,193,194,195,196]
def code : Code := WordCleanup.code banks

theorem entries_banks (layout : SplitNode.Layout) (k : ℕ) (clock childClock : List Bool)
    (header : ℕ→ℕ) : (entries layout k clock childClock header).map Prod.fst=banks := rfl

theorem known_words (layout : SplitNode.Layout) (k : ℕ) (clock childClock : List Bool)
    (header : ℕ→ℕ) (s : BitRAMState) (h : State layout k clock childClock header s) :
    ∀a∈entries layout k clock childClock header,Word s a.1 a.2 := by
  intro a ha
  simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact by simpa only [SplitNode.Layout.child] using h.child.parentWidth
  · exact h.child.index
  · exact h.route.oldJump
  · exact h.child.clock
  · exact h.route.oldMinimum
  · exact h.route.newJump
  · exact h.child.one
  · exact h.child.bitClock
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (h.workspace.1.2.2 88 (by simp [DoublingPass.Private]))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (h.workspace.1.2.2 89 (by simp [DoublingPass.Private]))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (h.workspace.1.2.2 90 (by simp [DoublingPass.Private]))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (h.workspace.1.2.2 91 (by simp [DoublingPass.Private]))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (h.workspace.1.2.2 92 (by simp [DoublingPass.Private]))
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h.zero94
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h.zero95
  · exact h.count
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h.zero97
  · exact h.inputA
  · exact h.inputB
  · exact h.saved.1
  · exact h.saved.2.1
  · exact h.saved.2.2.1
  · exact h.saved.2.2.2.1
  · exact h.saved.2.2.2.2.1
  · exact h.saved.2.2.2.2.2
  · exact h.child.childWidth
  · exact h.child.childClock
  · exact h.child.bases 0
  · exact h.child.bases 1
  · exact h.child.bases 2
  · exact h.child.bases 3
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h.zero126
  · exact h.childCount
  · exact h.child.colors
  · exact h.header 190 (by decide)
  · exact h.header 191 (by decide)
  · exact h.header 192 (by decide)
  · exact h.header 193 (by decide)
  · exact h.header 194 (by decide)
  · exact h.header 195 (by decide)
  · exact h.header 196 (by decide)

theorem executes (layout : SplitNode.Layout) (k : ℕ) (clock childClock : List Bool)
    (header : ℕ→ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : State layout k clock childClock header s.val) :
    ∃steps t, Executes input tape code steps s t ∧
      steps≤41*(6*WordCleanup.wordBudget (entries layout k clock childClock header)+4)+1 ∧
      (∀i∈banks,Blank t.val i) ∧ BinaryPrecision.Frame banks.toFinset s.val t.val := by
  have hb := WordCleanup.bounded_entries (entries layout k clock childClock header) s.val
    (known_words layout k clock childClock header s.val hs)
  rw [entries_banks] at hb
  obtain ⟨steps,t,he,hc,ht,hf⟩ := WordCleanup.executes banks _ input tape s hb
  exact ⟨steps,t,he,hc,ht,hf⟩

#print axioms known_words
#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Tree.NodeCleanup
