import Maxwell.Continuum.SourceRoutingAssemblyState

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def cleanupEntries (q : ℕ→ℕ) (k : ℕ) (clock childClock : List Bool) : List (ℕ×List Bool) :=
  [(80,(q 802).bits),(81,[]),(83,clock),(85,(q 805).bits),(86,[true]),(87,[false]),
   (96,(2*2^k).bits),(100,(q 800).bits),(120,(q 802-1).bits),(121,childClock),
   (122,(q 803).bits),(123,[]),(124,(q 804).bits),(125,[]),(126,[]),(127,(2^k).bits),(128,(q 805).bits)]

theorem cleanup_words (q : ℕ→ℕ) (k : ℕ) (clock childClock : List Bool)
    (s : BitRAMState) (hs : State q k clock childClock s) :
    ∀a∈cleanupEntries q k clock childClock,Word s a.1 a.2 := by
  intro a ha
  simp only [cleanupEntries,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hs.config.parentWidth
  · exact hs.config.index
  · exact hs.config.clock
  · exact hs.colorSource
  · exact hs.config.one
  · exact hs.config.bitClock
  · exact hs.count
  · exact hs.config.parent
  · exact hs.config.childWidth
  · exact hs.config.childClock
  · exact hs.config.bases 0
  · exact hs.config.bases 1
  · exact hs.config.bases 2
  · exact hs.config.bases 3
  · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr hs.zero126
  · exact hs.childCount
  · exact hs.config.colors

theorem cleanup_executes (q : ℕ→ℕ) (k : ℕ) (clock childClock : List Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : State q k clock childClock s.val) :
    ∃steps t,Executes input tape (WordCleanup.code live) steps s t ∧
      steps ≤ 17*(6*WordCleanup.wordBudget (cleanupEntries q k clock childClock)+4)+1 ∧
      NodeVisit.Clean t.val ∧ BinaryPrecision.Frame live.toFinset s.val t.val := by
  have hb:=WordCleanup.bounded_entries (cleanupEntries q k clock childClock) s.val
    (cleanup_words q k clock childClock s.val hs)
  change WordCleanup.Bounded live _ s.val at hb
  obtain ⟨steps,t,he,hcost,zt,ft⟩:=WordCleanup.executes live _ input tape s hb
  refine ⟨steps,t,he,hcost,⟨?_,?_⟩,ft⟩
  · apply DoublingInit.workspace_of_tapes (s:=s.val) (w:=hs.workspace)
    intro i hi
    apply ft.tapes
    simp only [List.mem_toFinset,live,List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with hi|hi
    · omega
    · simp only [DoublingInit.Private,DoublingPass.Private] at hi;omega
  · intro i hi
    by_cases hl : i∈live
    · exact zt i hl
    · exact RationalAccumulator.blank_of_eq (ft.tapes i (by simpa using hl)) (hs.unused i hi hl)

theorem cleanup_budget (q : ℕ→ℕ) (k B : ℕ) (_hB : 1 ≤ B)
    (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈controls,(q i).bits.length ≤ B)
    (clock childClock : List Bool) (hc : clock.length=q 802) (hcc : childClock.length=q 802-1) :
    WordCleanup.wordBudget (cleanupEntries q k clock childClock) ≤ 17*(B+2) := by
  have h0:=hq 800 (by decide)
  have h1:=hq 801 (by decide)
  have h2:=hq 802 (by decide)
  have h3:=hq 803 (by decide)
  have h4:=hq 804 (by decide)
  have h5:=hq 805 (by decide)
  have count := NodeSetup.clock_length q k hn
  have childCount := (Maxwell.Continuum.RationalWords.bits_mono (show 2^k ≤ 2*2^k by omega))
  have childWidth := (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (q 802) 1)).trans h2
  simp only [cleanupEntries,WordCleanup.wordBudget,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,hc,hcc]
  rw [hn] at count h1
  omega

#print axioms cleanup_executes
#print axioms cleanup_budget
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
