import Maxwell.Cost.SourceCircuit.ScanBits
import Maxwell.Cost.SourceCircuit.SeekEnd

namespace Maxwell.Cost.SourceCircuit.Marker
open Structured

def code : Code := .seq (ScanBits.readCode 24) (.atom (.tapeRight 24))

theorem executes (input : List Bool) (tape : ℕ → Bool) (preceding following : List Bool)
    (bit : Bool) (s : Store)
    (hs : s.val.tapes 24 = Increment.cursor preceding (bit::following) 0) :
    ∃ t, Executes input tape code 5 s t ∧ t.val.registers 30 = bit ∧
      t.val.registers 31 = true ∧
      t.val.tapes 24 = Increment.cursor (preceding ++ [bit]) following 0 ∧
      ScanBits.Passive 24 s t := by
  let r := ScanBits.checked 24 s
  let t := ScanBits.advanced 24 r
  have read : (s.val.tapes 24).read = some bit := by
    rw [hs]
    exact Increment.cursor_read preceding (bit::following) 0
  refine ⟨t,(ScanBits.read_executes 24 input tape s).seq (Executes.tapeRight input tape r 24),
    by simp [t,r,ScanBits.advanced,ScanBits.checked,Store.ofState,BitRAMState.setTape,read],
    by simp [t,r,ScanBits.advanced,ScanBits.checked,Store.ofState,BitRAMState.setTape,read],?_,
    SeekEnd.passive_trans (ScanBits.checked_passive 24 s) (ScanBits.advanced_passive 24 r)⟩
  simp [t,r,ScanBits.advanced,ScanBits.checked,Store.ofState,BitRAMState.setTape,hs,
    Increment.cursor,List.append_assoc,Nat.cast_add]

end Maxwell.Cost.SourceCircuit.Marker
