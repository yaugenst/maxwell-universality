import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.DecoderTerm
open Structured

def saveSign : BitRAM := ⟨[.literal 65 false, .bitXor 65 23 65, .halt]⟩
def saveState (s : BitRAMState) : BitRAMState :=
  {s with pc := 2, registers := Function.update s.registers 65 (s.registers 23)}

theorem saveSign_steps (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call saveSign) 3 s (Store.ofState (saveState s.val)) := by
  have h : PricedSteps (saveSign.next input tape) 2 s.val (saveState s.val) := by
    apply executeInstructions_sound (instructions := 2)
    simp [executeInstructions,BitRAM.next,saveSign,s.property,saveState,BitRAMState.setRegister]
  exact .call _ _ _ _ h rfl

def finishSign : BitRAM := ⟨[.bitXor 35 23 65, .literal 23 false, .bitXor 23 65 23, .halt]⟩
def signState (s : BitRAMState) : BitRAMState :=
  {s with pc := 3, registers := (Function.update
    (Function.update s.registers 35 (Bool.xor (s.registers 23) (s.registers 65))) 23 (s.registers 65))}

theorem finishSign_steps (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call finishSign) 4 s (Store.ofState (signState s.val)) := by
  have h : PricedSteps (finishSign.next input tape) 3 s.val (signState s.val) := by
    apply executeInstructions_sound (instructions := 3)
    simp [executeInstructions,BitRAM.next,finishSign,s.property,signState,BitRAMState.setRegister]
  exact .call _ _ _ _ h rfl

end Maxwell.Cost.DecoderTerm
