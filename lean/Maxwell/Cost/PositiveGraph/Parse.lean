import Maxwell.Cost.SparseEmission.ReadField
import Maxwell.Cost.SparseEmission.GateBinding

namespace Maxwell.Cost.PositiveGraph.Parse
open Structured

def flagsProgram : BitRAM := ⟨[.readTape 110 44 46,.tapeRight 110,
  .readTape 110 45 46,.tapeRight 110,.halt]⟩
def code : Code := .seq (SparseEmission.ReadField.code 110 93 111)
  (.seq (SparseEmission.ReadField.code 110 93 112)
    (.seq (.call flagsProgram)
      (.seq (.call (Rewind.program 111)) (.call (Rewind.program 112)))))

def flagsState (s : BitRAMState) (negative half : Bool) : BitRAMState :=
  {s with
    pc := 4
    registers := Function.update (Function.update (Function.update s.registers 44 negative) 45 half) 46 true
    tapes := Function.update s.tapes 110 (SparseEmission.ReadGate.advance (s.tapes 110) 2)}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 110 → i ≠ 111 → i ≠ 112 → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 44 → i ≠ 45 → i ≠ 46 → t.registers i = s.registers i

theorem flags_executes (input : List Bool) (randomTape : ℕ → Bool) (negative half : Bool)
    (suffix : List Bool) (s : Store)
    (hs : TapeRepresents (s.val.tapes 110) (negative::half::suffix)) :
    Executes input randomTape (.call flagsProgram) 7 s (Store.ofState (flagsState s.val negative half)) := by
  have h0 : (s.val.tapes 110).cells (s.val.tapes 110).head = some negative := by simpa using hs 0
  have h1 : (s.val.tapes 110).cells ((s.val.tapes 110).head+1) = some half := by simpa using hs 1
  apply Executes.call flagsProgram s (flagsState s.val negative half) 6
  · apply executeInstructions_sound (instructions := 4)
    simp [executeInstructions,flagsProgram,BitRAM.next,s.property,BitRAMState.setRegister,
      BitRAMState.setTape,BitTape.read,h0,h1,flagsState,SparseEmission.ReadGate.advance,add_assoc]
    funext i
    by_cases hi : i = 46 <;> simp [Function.update_apply,hi]
  · rfl

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (row column clock suffix : List Bool) (negative half : Bool) (clockOrigin : ℤ) (s : Store)
    (hcolumn : column.length = row.length) (hclock : clock.length = row.length)
    (hs : TapeRepresents (s.val.tapes 110) (row++column++[negative,half]++suffix))
    (h93 : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank) :
    ∃ t, Executes input randomTape code (36*row.length+39) s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (2*row.length+2) ∧
      TapeRepresents (t.val.tapes 110) suffix ∧
      t.val.tapes 111 = BitTape.shifted row 0 ∧ t.val.tapes 112 = BitTape.shifted column 0 ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧ Frame s.val t.val := by
  obtain ⟨a,ea,a110,a111,aa,am,af,ak⟩ := SparseEmission.ReadField.executes 110 93 111
    (by decide) (by decide) (by decide) input randomTape row (column++[negative,half]++suffix)
    clock clockOrigin s hclock h93 (by simpa [List.append_assoc] using hs) h111
  have aSuffix : TapeRepresents (a.val.tapes 110) (column++[negative,half]++suffix) := by
    rw [a110]
    exact SparseEmission.ReadGate.advance_represents _ row _ (by simpa [List.append_assoc] using hs)
  obtain ⟨b,eb,b110,b112,ba,bm,bf,bk⟩ := SparseEmission.ReadField.executes 110 93 112
    (by decide) (by decide) (by decide) input randomTape column ([negative,half]++suffix)
    clock clockOrigin a (hclock.trans hcolumn.symm) ((ak 93 (by decide) (by decide)).trans h93)
    (by simpa [List.append_assoc] using aSuffix) ((ak 112 (by decide) (by decide)).trans h112)
  have bSuffix : TapeRepresents (b.val.tapes 110) ([negative,half]++suffix) := by
    rw [b110]
    exact SparseEmission.ReadGate.advance_represents _ column _ (by simpa [List.append_assoc] using aSuffix)
  let c := Store.ofState (flagsState b.val negative half)
  have ec : Executes input randomTape (.call flagsProgram) 7 b c := flags_executes input randomTape negative half suffix b bSuffix
  have c111 : c.val.tapes 111 = BitTape.shiftedEnd row 0 := by
    simpa [c,Store.ofState,flagsState,BitTape.atEnd,BitTape.shiftedEnd,BitTape.shifted,BitTape.ofList]
      using (bk 111 (by decide) (by decide)).trans a111
  have c112 : c.val.tapes 112 = BitTape.shiftedEnd column 0 := by
    simpa [c,Store.ofState,flagsState,BitTape.atEnd,BitTape.shiftedEnd,BitTape.shifted,BitTape.ofList] using b112
  obtain ⟨edSteps,d111⟩ := WordTransfer.rewind_shifted 111 0 input randomTape row c.val c.property c111
  let d := Store.ofState (Rewind.finishAt 111 0 c.val)
  have ed : Executes input randomTape (.call (Rewind.program 111)) (4*row.length+6) c d := .call _ _ _ _ edSteps rfl
  have d112 : d.val.tapes 112 = BitTape.shiftedEnd column 0 := by simpa [d,Store.ofState,Rewind.finishAt] using c112
  obtain ⟨etSteps,t112⟩ := WordTransfer.rewind_shifted 112 0 input randomTape column d.val d.property d112
  let t := Store.ofState (Rewind.finishAt 112 0 d.val)
  have et : Executes input randomTape (.call (Rewind.program 112)) (4*column.length+6) d t := .call _ _ _ _ etSteps rfl
  have keep (i : ℕ) (h110 : i ≠ 110) (h111i : i ≠ 111) (h112i : i ≠ 112) :
      t.val.tapes i = s.val.tapes i := by
    simp only [t,d,c,Store.ofState,Rewind.finishAt,flagsState,Function.update_of_ne h110,
      Function.update_of_ne h111i,Function.update_of_ne h112i]
    exact (bk i h110 h112i).trans (ak i h110 h111i)
  have source : t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (2*row.length+2) := by
    simp only [t,d,c,Store.ofState,Rewind.finishAt,flagsState,Function.update_of_ne (by decide : (110:ℕ) ≠ 112),
      Function.update_of_ne (by decide : (110:ℕ) ≠ 111),Function.update_self]
    rw [b110]
    change SparseEmission.ReadGate.advance (SparseEmission.ReadGate.advance (a.val.tapes 110) column.length) 2 = _
    rw [a110]
    simp only [SparseEmission.ReadGate.advance, Nat.cast_add, Nat.cast_mul]
    congr 1
    rw [hcolumn]
    ring
  refine ⟨t,?_,source,?_,?_,t112,?_,?_,?_⟩
  · convert ea.seq (eb.seq (ec.seq (ed.seq et))) using 1 <;> first | rfl | omega
  · rw [source]
    have hh := SparseEmission.ReadGate.advance_represents _ (row++column++[negative,half]) suffix hs
    simpa [hcolumn,two_mul,add_assoc] using hh
  · simpa [t,d,Store.ofState,Rewind.finishAt] using d111
  · simp [t,d,c,Store.ofState,Rewind.finishAt,flagsState]
  · simp [t,d,c,Store.ofState,Rewind.finishAt,flagsState]
  · refine ⟨ba.trans aa,bm.trans am,bf.inputHead.trans af.inputHead,
      bf.randomCursor.trans af.randomCursor,bf.output.trans af.output,keep,?_,?_⟩
    · simpa [t,d,c,Store.ofState,Rewind.finishAt,flagsState] using bf.sign.trans af.sign
    · intro i hi h44 h45 h46
      simpa [t,d,c,Store.ofState,Rewind.finishAt,flagsState,h44,h45,h46,
        show i ≠ 24 by omega,show i ≠ 25 by omega] using (bf.control i hi).trans (af.control i hi)

end Maxwell.Cost.PositiveGraph.Parse
