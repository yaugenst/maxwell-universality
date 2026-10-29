import Maxwell.Cost.RealPrivate.StoreSemantics
import Maxwell.Cost.RealPrivate.ControlInstructions

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem input_instruction (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) (dst address : ℕ) :
    ∃ cost t, cost ≤ 2 * L.realInputStride + 39 ∧
      Executes externalInput tape (instruction L (.input dst address)) cost s t ∧
      Represents origin (source.setWord dst (sourceInput.words (source.indices address)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  obtain ⟨cost, t, hc, he, ht, hv, hf⟩ := readRealInput_correct externalInput sourceInput tape _
    hg.2.1 (hg.2.2.2.inputs h.high hi)
  rw [hg.2.2.1] at hv
  have hs := setWord_correct externalInput tape t ht dst 0
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  exact ⟨6 + (cost + (25 + 2)), _, by omega, hg.1.seq (he.seq (hs.1.seq hp.1)),
    hp.2.1, hg.2.2.2.trans (hf.trans (hs.2.2.trans hp.2.2))⟩

theorem inputIndex_instruction (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) (dst address : ℕ) :
    ∃ cost t, cost ≤ 2 * L.indexInputStride + 39 ∧
      Executes externalInput tape (instruction L (.inputIndex dst address)) cost s t ∧
      Represents origin (source.setIndex dst (sourceInput.indices (source.indices address)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  obtain ⟨cost, t, hc, he, ht, hv, hf⟩ := readIndexInput_correct externalInput sourceInput tape _
    hg.2.1 (hg.2.2.2.inputs h.high hi)
  rw [hg.2.2.1] at hv
  have hs := setIndex_correct externalInput tape t ht dst valueRegister (by decide)
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  exact ⟨6 + (cost + (25 + 2)), _, by omega, hg.1.seq (he.seq (hs.1.seq hp.1)),
    hp.2.1, hg.2.2.2.trans (hf.trans (hs.2.2.trans hp.2.2))⟩

theorem random_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.randomBit dst)) 29 s t ∧
      Represents origin
        {source.setWord dst (if tape source.randomCursor then 1 else 0) with
          randomCursor := source.randomCursor + 1} (dst :: written) t.val ∧
      CallerFrame origin s.val t.val := by
  let b := tape s.val.randomCursor
  let s0 := drawn s 0 b
  have h0 := h.drawn 0 b (by have := h.high; omega)
  have hs := setWord_correct externalInput tape s0 h0 dst 0
  have hv : s0.val.words 0 = if tape source.randomCursor then 1 else 0 := by
    simp [s0, drawn, b, h.random_cursor]
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, (randomBit_executes externalInput tape s 0).seq (hs.1.seq hp.1), hp.2.1, ?_⟩
  exact (callerFrame_drawn s origin 0 b (by decide)).trans (hs.2.2.trans hp.2.2)

end Maxwell.Cost.RealPrivate
