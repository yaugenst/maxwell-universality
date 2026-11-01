import Maxwell.Cost.ZeroSource.Format
import Maxwell.Cost.EmitRows

namespace Maxwell.Cost.ZeroSource
open Structured

def emitCode : Code := EmitRows.code header row
def emitBound (n : ℕ) : ℕ := EmitRows.bound header row n

theorem emit_steps (n : ℕ) (dimensionOrigin counterOrigin : ℤ)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hn : s.val.tapes 19 = BitTape.shifted n.bits dimensionOrigin)
    (hc : s.val.tapes 90 = {BitTape.blank with head := counterOrigin}) :
    ∃ cost, ∃ t : Store, Executes input randomTape emitCode cost s t ∧
      cost ≤ emitBound n ∧ t.val.output = (targetBits n).reverse ++ s.val.output ∧
      t.val.randomCursor = s.val.randomCursor := by
  simpa only [emitCode,emitBound,targetBits,EmitRows.bits] using
    EmitRows.executes header row n dimensionOrigin counterOrigin input randomTape s hn hc

end Maxwell.Cost.ZeroSource
