import Maxwell.Cost.RealPrivate.Cleanup

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def initialized (s : Store) : Store :=
  (((((((s.put zeroRegister 0).put oneRegister 1).put statusRegister 0).put
    realOutputLength 0).put indexOutputLength 0).put logLength 0).put sourcePC 0).put activeRegister 1

theorem initializeState_executes (externalInput : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes externalInput tape initializeState 16 s (initialized s) := by
  let s0 := s.put zeroRegister 0
  let s1 := s0.put oneRegister 1
  let s2 := s1.put statusRegister 0
  let s3 := s2.put realOutputLength 0
  let s4 := s3.put indexOutputLength 0
  let s5 := s4.put logLength 0
  let s6 := s5.put sourcePC 0
  exact (literal_executes externalInput tape s zeroRegister 0).seq
    ((literal_executes externalInput tape s0 oneRegister 1).seq
      ((literal_executes externalInput tape s1 statusRegister 0).seq
        ((literal_executes externalInput tape s2 realOutputLength 0).seq
          ((literal_executes externalInput tape s3 indexOutputLength 0).seq
            ((literal_executes externalInput tape s4 logLength 0).seq
              ((literal_executes externalInput tape s5 sourcePC 0).seq
                (literal_executes externalInput tape s6 activeRegister 1)))))))

theorem initialized_represents (origin : ℕ) (s : Store) (high : 256 ≤ origin)
    (ho : s.val.indices originRegister = origin) (empty : Cleanup.EmptyBank origin s.val) :
    Represents origin {RAMState.initial with randomCursor := s.val.randomCursor} [] (initialized s).val := by
  have hn (a j : ℕ) (hj : j < 256) : slot origin 0 a ≠ j := slot_ne_small high 0 a j hj
  refine ⟨high, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [initialized, originRegister, zeroRegister, oneRegister, statusRegister,
      realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister] using ho
  · simp [initialized, zeroRegister, oneRegister, statusRegister, realOutputLength,
      indexOutputLength, logLength, sourcePC, activeRegister]
  · simp [initialized, zeroRegister, oneRegister, statusRegister, realOutputLength,
      indexOutputLength, logLength, sourcePC, activeRegister]
  · simp [initialized, RAMState.initial, sourcePC, activeRegister]
  · intro a; exact (empty a).1
  · intro a
    simpa [initialized, hn, zeroRegister, oneRegister, statusRegister, realOutputLength,
      indexOutputLength, logLength, sourcePC, activeRegister, RAMState.initial] using (empty a).2
  · simp [initialized, RAMState.initial, realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister]
  · simp [initialized, RAMState.initial, indexOutputLength, logLength, sourcePC, activeRegister]
  · intro j hj; simp [RAMState.initial] at hj
  · intro j hj; simp [RAMState.initial] at hj
  · simp [initialized, logLength, sourcePC, activeRegister]
  · intro j hj; simp at hj

theorem initialized_inputs {origin : ℕ} {L : Layout} {B : InputBuffer} {sourceInput : RAMInput}
    (s : Store) (hi : Inputs L origin B sourceInput s.val) :
    Inputs L origin B sourceInput (initialized s).val := by
  refine ⟨?_, ?_, ?_, ?_, hi.real_low, hi.index_low, hi.real_high, hi.index_high,
    hi.real_cells, ?_, hi.real_outside, hi.index_outside⟩
  · simpa [initialized, realInputBase, zeroRegister, oneRegister, statusRegister,
      realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister] using hi.real_base
  · simpa [initialized, realInputLength, zeroRegister, oneRegister, statusRegister,
      realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister] using hi.real_length
  · simpa [initialized, indexInputBase, zeroRegister, oneRegister, statusRegister,
      realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister] using hi.index_base
  · simpa [initialized, indexInputLength, zeroRegister, oneRegister, statusRegister,
      realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister] using hi.index_length
  · intro j hj
    have hn (r : ℕ) (hr : r < 256) : B.indexBase + L.indexInputStride * j ≠ r := by
      have := hi.index_low
      omega
    simpa [initialized, hn, zeroRegister, oneRegister, statusRegister, realOutputLength,
      indexOutputLength, logLength, sourcePC, activeRegister] using hi.index_cells j hj

theorem initialized_control (s : Store) :
    (initialized s).val.indices fuelRegister = s.val.indices fuelRegister ∧
    (initialized s).val.indices statusRegister = 0 ∧
    (initialized s).val.indices activeRegister = 1 ∧
    (initialized s).val.randomCursor = s.val.randomCursor ∧
    (initialized s).val.output = s.val.output ∧
    (initialized s).val.indexOutput = s.val.indexOutput := by
  simp [initialized, fuelRegister, zeroRegister, oneRegister, statusRegister,
    realOutputLength, indexOutputLength, logLength, sourcePC, activeRegister, Store.put]

theorem initial_covered (randomCursor : ℕ) :
    Covered {RAMState.initial with randomCursor := randomCursor} [] := by
  intro a _
  exact ⟨rfl, rfl⟩

end Maxwell.Cost.RealPrivate
