import Maxwell.Cost.PositiveGraph.Loop
import Maxwell.Cost.PositiveGraph.Cursors
import Maxwell.Cost.PositiveGraph.Bounds

namespace Maxwell.Cost.PositiveGraph.Pass
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq InitializeCursors.code Loop.passCode
def program : BitRAM := code.compile
def price (width dimension count base : ℕ) : ℕ :=
  600000*(count+1)*(bitBudget width dimension count base+2)^2

/-- Starting from the stored sparse archive and initialized physical
arrays, one fixed program constructs every positive endpoint and diagonal. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count base : ℕ) (entries : List (BoundedEntry dimension))
    (sourceClock endpointClock diagonalClock : List Bool) (s : Store)
    (hlen : entries.length = count) (hcount : count ≤ 3*dimension)
    (hdimension : dimension < 2^width) (hsep : 4*count*(width+3) ≤ base)
    (hd : Descriptor width dimension base sourceClock endpointClock diagonalClock s.val)
    (hw : Workspace s.val) (h118 : Blank s.val 118) (h119 : Blank s.val 119) (h121 : Blank s.val 121)
    (h153 : BankArray.Word s.val 153 (2*count).bits) (h154 : BankArray.Word s.val 154 (2*dimension).bits)
    (tables : Tables dimension count) (htables : tables.Represents width base s.val.memory)
    (hsource : TapeRepresents (s.val.tapes 110) (recordsWire width entries)) :
    ∃ cost t, cost ≤ price width dimension count base ∧ Executes input randomTape code cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (recordsWire width entries).length ∧
      t.val.memory = foldMemory width dimension count 0 base entries (by omega) tables s.val.memory ∧
      (foldTables width dimension count 0 entries (by omega) tables).Represents width base t.val.memory ∧
      Descriptor width dimension base sourceClock endpointClock diagonalClock t.val ∧
      Cursors dimension count count t.val ∧ Workspace t.val ∧ Frame workBanks s.val t.val := by
  obtain ⟨a,ea,ac,am,af,ak⟩ := InitializeCursors.executes input randomTape dimension count s
    h153 h154 h118 h119 h121
  have aframe : Frame workBanks s.val a.val := af.mono (by decide)
  have ad := hd.of_frame aframe
  have aw : Workspace a.val :=
    ⟨SourceCircuit.scratch_of_tapes hw.scratch (fun i hi => ak i (by omega) (by omega)),
      RationalAccumulator.blank_of_eq (ak 7 (by decide) (by decide)) hw.sample,
      RationalAccumulator.blank_of_eq (ak 37 (by decide) (by decide)) hw.packed,
      RationalAccumulator.blank_of_eq (ak 120 (by decide) (by decide)) hw.payload,
      RationalAccumulator.blank_of_eq (ak 122 (by decide) (by decide)) hw.shiftedColumn,
      (ak 111 (by decide) (by decide)).trans hw.row,(ak 112 (by decide) (by decide)).trans hw.column⟩
  obtain ⟨lc,t,lcBound,et,t110,tm,tt,td,tc,tw,_test,tf⟩ := Loop.pass input randomTape
    width dimension count 0 base entries sourceClock endpointClock diagonalClock a
    (by omega) hcount hdimension hsep ad ac aw tables
    (by simpa only [am] using htables) (by simpa only [ak 110 (by decide) (by decide)] using hsource)
  refine ⟨_,t,?_,ea.seq et,?_,?_,tt,td,by simpa only [zero_add,hlen] using tc,tw,aframe.trans tf⟩
  · have hb := fold_price_le width dimension count 0 base diagonalClock entries (by omega) tables hd.diagonalClock_length
    have hcBits : (2*count).bits.length ≤ bitBudget width dimension count base :=
      (bits_mono (show 2*count ≤ 4*count+1 by omega)).trans (by unfold bitBudget; omega)
    have hdBits : (2*dimension).bits.length ≤ bitBudget width dimension count base :=
      (bits_mono (show 2*dimension ≤ 2*dimension+count+1 by omega)).trans (by unfold bitBudget; omega)
    have hb' := hb.trans (show entries.length*(500000*(bitBudget width dimension count base+2)^2+4)+1 ≤
        count*(500000*(bitBudget width dimension count base+2)^2+4)+1 by rw [hlen])
    let Q := (bitBudget width dimension count base+2)^2
    have hQ : 4 ≤ Q := by dsimp [Q]; nlinarith
    have hBQ : bitBudget width dimension count base ≤ Q := by dsimp [Q]; nlinarith
    have hprefix : 15*((2*count).bits.length+(2*dimension).bits.length)+34 ≤ 1000*Q := by omega
    have hloop : lc ≤ count*(500000*Q+4)+4 := by dsimp [Q]; omega
    have hunit : 500000*Q+4 ≤ 500001*Q := by omega
    change _ ≤ 600000*(count+1)*Q
    calc
      _ ≤ 1000*Q+(count*(500000*Q+4)+4) := Nat.add_le_add hprefix hloop
      _ ≤ 1000*Q+(count*(500001*Q)+Q) := Nat.add_le_add_left
        (Nat.add_le_add (Nat.mul_le_mul_left count hunit) hQ) _
      _ = (500001*count+1001)*Q := by ring
      _ ≤ 600000*(count+1)*Q := Nat.mul_le_mul_right Q (by omega)
  · rw [t110,ak 110 (by decide) (by decide)]
  · simpa only [am] using tm

theorem run (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count base : ℕ) (entries : List (BoundedEntry dimension))
    (sourceClock endpointClock diagonalClock : List Bool) (s : Store)
    (hlen : entries.length = count) (hcount : count ≤ 3*dimension)
    (hdimension : dimension < 2^width) (hsep : 4*count*(width+3) ≤ base)
    (hd : Descriptor width dimension base sourceClock endpointClock diagonalClock s.val)
    (hw : Workspace s.val) (h118 : Blank s.val 118) (h119 : Blank s.val 119) (h121 : Blank s.val 121)
    (h153 : BankArray.Word s.val 153 (2*count).bits) (h154 : BankArray.Word s.val 154 (2*dimension).bits)
    (tables : Tables dimension count) (htables : tables.Represents width base s.val.memory)
    (hsource : TapeRepresents (s.val.tapes 110) (recordsWire width entries)) :
    ∃ t : Store, (runPriced (program.next input randomTape) (price width dimension count base+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (program.next input randomTape) (price width dimension count base+1) s.val).instructions ≤
        price width dimension count base ∧
      t.val.memory = foldMemory width dimension count 0 base entries (by omega) tables s.val.memory ∧
      (foldTables width dimension count 0 entries (by omega) tables).Represents width base t.val.memory ∧
      Descriptor width dimension base sourceClock endpointClock diagonalClock t.val ∧
      Cursors dimension count count t.val ∧ Workspace t.val ∧ Frame workBanks s.val t.val := by
  obtain ⟨cost,t,hcost,he,_ts,tm,tt,td,tc,tw,tf⟩ := executes input randomTape width dimension count base
    entries sourceClock endpointClock diagonalClock s hlen hcount hdimension hsep hd hw h118 h119 h121
    h153 h154 tables htables hsource
  have hr := he.compiled_run (price width dimension count base+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,tm,tt,td,tc,tw,tf⟩

end Maxwell.Cost.PositiveGraph.Pass
