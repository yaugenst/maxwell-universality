import Maxwell.Cost.SparseEmission.Execute
import Maxwell.Cost.SparseEmission.Values

namespace Maxwell.Cost.SparseEmission
open Structured
open RationalAccumulator (Blank)

def program : BitRAM := code.compile

/-- Literal source specialization, with a bounded run of one fixed finite
BitRAM program and the exact sparse matrix archive at completion. -/
theorem source_run (S : Source.SparseSystem) (precision : ℕ)
    (input : List Bool) (randomTape : ℕ → Bool) (width : ℕ) (bytes clock : List Bool)
    (clockOrigin : ℤ) (s : Store)
    (hwidth : 0 < width) (hfit : (Logical.sourceCircuit S precision).size < 2^width)
    (hc : clock.length = width)
    (hbytes : SourceCircuit.traceBytes width (Logical.sourceCircuit_rational S precision).code.trace = some bytes)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hn : BankArray.Word s.val 19 S.n.bits)
    (hclock : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (h97 : s.val.tapes 97 = BitTape.atEnd bytes)
    (h105 : s.val.tapes 105 = BitTape.atEnd
      ((List.ofFn (fun i : Fin S.n => (Logical.sourceOutput S precision i).val)).flatMap
        (SourceCircuit.fixedWidth width)))
    (h110 : s.val.tapes 110 = BitTape.blank)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank)
    (h113 : s.val.tapes 113 = BitTape.blank) (h114 : s.val.tapes 114 = BitTape.blank)
    (h115 : s.val.tapes 115 = BitTape.blank) :
    ∃ t : Store,
      (runPriced (program.next input randomTape)
        (1000*((Logical.sourceCircuit S precision).size+1)*(width+1)+1) s.val).finished =
          some (t.place code.size) ∧
      (runPriced (program.next input randomTape)
        (1000*((Logical.sourceCircuit S precision).size+1)*(width+1)+1) s.val).instructions ≤
          1000*((Logical.sourceCircuit S precision).size+1)*(width+1) ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (Logical.sourceSquareEntries S precision))
        (-(entriesWire width (Logical.sourceSquareEntries S precision)).length) ∧
      t.val.tapes 105 = BitTape.blank ∧ t.val.tapes 111 = BitTape.blank ∧
      t.val.tapes 112 = BitTape.blank ∧ t.val.tapes 114 = BitTape.blank ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧ OutputFrame s.val t.val := by
  obtain ⟨cost,t,hcost,execution,ha,hrest⟩ := executes
    (Logical.sourceCircuit_rational S precision).code (Logical.sourceOutput S precision)
    input randomTape width bytes clock clockOrigin s hwidth hfit hc hbytes hs h7 h37 hn hclock
    h97 h105 h110 h111 h112 h113 h114 h115
  have run := execution.compiled_run
    (1000*((Logical.sourceCircuit S precision).size+1)*(width+1)+1) (by omega)
  exact ⟨t,run.1,run.2.symm ▸ hcost,ha,hrest⟩

end Maxwell.Cost.SparseEmission
