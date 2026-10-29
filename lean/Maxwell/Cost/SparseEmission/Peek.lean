import Maxwell.Cost.SparseEmission.Common
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.SparseEmission
open Structured

def peekCode : Code := Code.atom (.readTape 97 40 43)
def peekState (s : Store) : Store := Store.ofState
  {s.val with pc := 1, registers := Function.update (Function.update s.val.registers 40
    ((s.val.tapes 97).read.getD false)) 43 ((s.val.tapes 97).read.isSome)}

theorem peek_executes (input : List Bool) (randomTape : ℕ → Bool) (s : Store) :
    Executes input randomTape peekCode 3 s (peekState s) := by
  apply Executes.atom (extra := 1)
  · simp [BitRAM.next,s.property,BitRAMState.setRegister]
  · rfl

theorem peek_frame (s : Store) : Frame s.val (peekState s).val := by
  constructor <;> intros <;> simp_all [peekState,Store.ofState]

@[simp] theorem peek_tapes (s : Store) : (peekState s).val.tapes = s.val.tapes := rfl

theorem peek_present (s : Store) (bytes : List Bool)
    (hs : TapeRepresents (s.val.tapes 97) bytes) :
    (peekState s).val.registers 43 = !bytes.isEmpty := by
  have h := hs 0
  cases bytes <;> simp_all [peekState,Store.ofState,BitTape.read]

end Maxwell.Cost.SparseEmission
