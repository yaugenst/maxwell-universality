import Maxwell.Cost.BankStack.Restore

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- A compiled save has a finite literal program and a uniform linear cap. -/
theorem save_run (clockBank stack : ℕ) (ids : List ℕ)
    (hc : 10 ≤ clockBank) (ha : 10 ≤ stack) (hc37 : clockBank≠37)
    (ha37 : stack≠37) (hca : clockBank≠stack) (valid : Valid clockBank stack ids)
    (input : List Bool) (tape : ℕ → Bool) (values : ℕ → ℕ)
    (clock preceding : List Bool) (hclock : 0<clock.length)
    (hfit : ∀ i∈ids, (values i).bits.length≤clock.length)
    (s : Store) (banks : Banks ids values s.val) (scratch : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (h37 : Blank s.val 37) (hclockBank : Word s.val clockBank clock)
    (hstack : s.val.tapes stack=BitTape.atEnd preceding) :
    ∃ t : Store,
      (runPriced ((saveCode clockBank stack ids).compile.next input tape)
        (ids.length*(100*clock.length+110)+2) s.val).finished=some (t.place (saveCode clockBank stack ids).size) ∧
      (runPriced ((saveCode clockBank stack ids).compile.next input tape)
        (ids.length*(100*clock.length+110)+2) s.val).instructions ≤ ids.length*(100*clock.length+110)+1 ∧
      t.val.tapes stack=BitTape.atEnd (preceding++wire clock.length ids values) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {37,stack} s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := save clockBank stack ids hc ha hc37 ha37 hca valid input tape values
    clock preceding hclock hfit s banks scratch h7 h37 hclockBank hstack
  have hr := he.compiled_run (ids.length*(100*clock.length+110)+2) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

/-- Restore uses the saved bits and clears the actual replaced words; it
never accesses the proof-level value map while running. -/
theorem restore_run (clockBank stack : ℕ) (ids : List ℕ)
    (hc : 10 ≤ clockBank) (ha : 10 ≤ stack) (hca : clockBank≠stack)
    (valid : Valid clockBank stack ids) (distinct : ids.Nodup)
    (input : List Bool) (tape : ℕ → Bool) (values : ℕ → ℕ) (current : ℕ → List Bool)
    (clock preceding : List Bool)
    (hfit : ∀ i∈ids, (values i).bits.length≤clock.length)
    (hcurrent : ∀ i∈ids, (current i).length≤clock.length)
    (s : Store) (banks : WordAssign.Bank ids s.val current) (scratch : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (hclockBank : Word s.val clockBank clock)
    (hstack : s.val.tapes stack=BitTape.atEnd (preceding++wire clock.length ids values)) :
    ∃ t : Store,
      (runPriced ((restoreCode clockBank stack ids).compile.next input tape)
        (ids.length*(37*clock.length+32)+2) s.val).finished=some (t.place (restoreCode clockBank stack ids).size) ∧
      (runPriced ((restoreCode clockBank stack ids).compile.next input tape)
        (ids.length*(37*clock.length+32)+2) s.val).instructions ≤ ids.length*(37*clock.length+32)+1 ∧
      t.val.tapes stack=BitTape.atEnd preceding ∧ Banks ids values t.val ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame (insert stack ids.toFinset) s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := restore clockBank stack ids hc ha hca valid distinct input tape values current
    clock preceding hfit hcurrent s banks scratch h7 hclockBank hstack
  have hr := he.compiled_run (ids.length*(37*clock.length+32)+2) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.BankStack
