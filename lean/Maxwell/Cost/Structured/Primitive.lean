import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.Structured

/-- A literal instruction followed by a real return. This is finite syntax;
its state effects and charge come from the BitRAM transition semantics. -/
def Code.atom (instruction : BitRAMInstruction) : Code := .call ⟨[instruction, .halt]⟩

/-- A one-instruction proof lifts to structured code without introducing a
new primitive or dropping the charged return. -/
theorem Executes.atom {input : List Bool} {randomTape : ℕ → Bool}
    (instruction : BitRAMInstruction) (s : Store) (t : BitRAMState) (extra : ℕ)
    (step : (BitRAM.mk [instruction, .halt]).next input randomTape s.val = some ⟨t, extra⟩)
    (hpc : t.pc = 1) :
    Executes input randomTape (Code.atom instruction) (extra + 2) s (Store.ofState t) := by
  have hsteps : PricedSteps (BitRAM.next ⟨[instruction, .halt]⟩ input randomTape)
      (extra + 1) s.val t := PricedSteps.step step (PricedSteps.refl _)
  exact Executes.call _ s t (extra + 1) hsteps (by simp [hpc])

theorem Executes.literal (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (register : ℕ) (value : Bool) :
    Executes input randomTape (Code.atom (.literal register value)) 2 s
      (Store.ofState (s.val.setRegister register value)) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

theorem Executes.bitNot (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (dst src : ℕ) :
    Executes input randomTape (Code.atom (.bitNot dst src)) 2 s
      (Store.ofState (s.val.setRegister dst (!s.val.registers src))) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

theorem Executes.bitXor (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (dst left right : ℕ) :
    Executes input randomTape (Code.atom (.bitXor dst left right)) 2 s
      (Store.ofState (s.val.setRegister dst (xor (s.val.registers left) (s.val.registers right)))) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

theorem Executes.bitAnd (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (dst left right : ℕ) :
    Executes input randomTape (Code.atom (.bitAnd dst left right)) 2 s
      (Store.ofState (s.val.setRegister dst (s.val.registers left && s.val.registers right))) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

theorem Executes.tapeRight (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (workTape : ℕ) :
    Executes input randomTape (Code.atom (.tapeRight workTape)) 2 s
      (Store.ofState (s.val.setTape workTape
        {s.val.tapes workTape with head := (s.val.tapes workTape).head + 1})) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setTape, s.property]

theorem Executes.tapeLeft (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (workTape : ℕ) :
    Executes input randomTape (Code.atom (.tapeLeft workTape)) 2 s
      (Store.ofState (s.val.setTape workTape
        {s.val.tapes workTape with head := (s.val.tapes workTape).head - 1})) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setTape, s.property]

theorem Executes.writeTape (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (workTape register : ℕ) :
    Executes input randomTape (Code.atom (.writeTape workTape register)) 2 s
      (Store.ofState (s.val.setTape workTape
        ((s.val.tapes workTape).write (some (s.val.registers register))))) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setTape, s.property]

theorem Executes.eraseTape (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (workTape : ℕ) :
    Executes input randomTape (Code.atom (.eraseTape workTape)) 2 s
      (Store.ofState (s.val.setTape workTape ((s.val.tapes workTape).write none))) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setTape, s.property]

theorem Executes.readMemory (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (register : ℕ) :
    Executes input randomTape (Code.atom (.readMemory register)) (s.val.address.length + 2) s
      (Store.ofState (s.val.setRegister register (s.val.memory (addressValue s.val.address)))) := by
  apply Executes.atom
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

theorem Executes.output (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (register : ℕ) :
    Executes input randomTape (Code.atom (.output register)) 2 s
      (Store.ofState {s.val with pc := 1, output := s.val.registers register :: s.val.output}) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property]
  · rfl

end Maxwell.Cost.Structured
