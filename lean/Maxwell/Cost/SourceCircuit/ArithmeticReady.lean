import Maxwell.Cost.SourceCircuit.ArithmeticData
import Maxwell.Cost.SourceCircuit.CompileRecord
import Maxwell.Cost.SourceCircuit.Marker
import Maxwell.Cost.Structured.Footprint

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass
open Structured
open RationalAccumulator (Blank)

structure Ready (clock : List Bool) (precision : ℕ) (d : Data) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank7 : Blank s.val 7
  blank94 : Blank s.val 94
  blank96 : Blank s.val 96
  blank99 : Blank s.val 99
  blank103 : s.val.tapes 103 = BitTape.blank
  next : BankArray.Word s.val 95 d.next
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  terms : s.val.tapes 104 = BitTape.atEnd d.terms.flatten
  outputs : s.val.tapes 105 = BitTape.atEnd d.outputs
  counter : BankArray.Word s.val 106 d.counter
  clock : BankArray.Word s.val 93 clock
  power : BankArray.Word s.val 82 (2^precision).bits
  blank10 : s.val.tapes 10 = BitTape.blank
  blank15 : s.val.tapes 15 = BitTape.blank
  blank16 : s.val.tapes 16 = BitTape.blank
  blank83 : Blank s.val 83

theorem Ready.of_tapes {clock : List Bool} {precision : ℕ} {d : Data} {s t : Store}
    (h : Ready clock precision d s)
    (keep : ∀ j, j ≠ 24 → j ≠ 100 → t.val.tapes j = s.val.tapes j) : Ready clock precision d t :=
  ⟨scratch_of_tapes h.scratch (fun j hj => keep j (by omega) (by omega)),
    RationalAccumulator.blank_of_eq (keep 7 (by omega) (by omega)) h.blank7,
    RationalAccumulator.blank_of_eq (keep 94 (by omega) (by omega)) h.blank94,
    RationalAccumulator.blank_of_eq (keep 96 (by omega) (by omega)) h.blank96,
    RationalAccumulator.blank_of_eq (keep 99 (by omega) (by omega)) h.blank99,
    (keep 103 (by omega) (by omega)).trans h.blank103,
    BankArray.word_of_eq (keep 95 (by omega) (by omega)) h.next,
    (keep 97 (by omega) (by omega)).trans h.gates,
    (keep 104 (by omega) (by omega)).trans h.terms,
    (keep 105 (by omega) (by omega)).trans h.outputs,
    BankArray.word_of_eq (keep 106 (by omega) (by omega)) h.counter,
    BankArray.word_of_eq (keep 93 (by omega) (by omega)) h.clock,
    BankArray.word_of_eq (keep 82 (by omega) (by omega)) h.power,
    (keep 10 (by omega) (by omega)).trans h.blank10,
    (keep 15 (by omega) (by omega)).trans h.blank15,
    (keep 16 (by omega) (by omega)).trans h.blank16,
    RationalAccumulator.blank_of_eq (keep 83 (by omega) (by omega)) h.blank83⟩

theorem Ready.count {clock : List Bool} {precision : ℕ} {d : Data} {s t : Store}
    (h : Ready clock precision d s) (f : Counted.Frame 100 s t) : Ready clock precision d t :=
  h.of_tapes (fun j _ hj => f.2.2.2.2.2.1 j hj)

theorem Ready.marker {clock : List Bool} {precision : ℕ} {d : Data} {s t : Store}
    (h : Ready clock precision d s) (f : ScanBits.Passive 24 s t) : Ready clock precision d t :=
  h.of_tapes (fun j hj _ => f.tapes j hj)

def work : Finset ℕ := insert 24 (insert 100 (insert 105 CompileRecord.work))

structure Persistent (s t : Store) : Prop where
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j

theorem Persistent.refl (s : Store) : Persistent s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩

theorem Persistent.trans {s t u : Store} (h : Persistent s t) (k : Persistent t u) : Persistent s u :=
  ⟨k.memory.trans h.memory,k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,
    k.output.trans h.output,fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn)⟩

theorem persistent_count {s t : Store} (h : Counted.Frame 100 s t) : Persistent s t := by
  refine ⟨h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro j _ hj
  exact h.2.2.2.2.2.1 j (fun he => hj (by simp [work,he]))

theorem persistent_marker {s t : Store} (h : ScanBits.Passive 24 s t) : Persistent s t := by
  refine ⟨h.memory,h.inputHead,h.randomCursor,h.output,?_⟩
  intro j _ hj
  exact h.tapes j (fun he => hj (by simp [work,he]))

theorem persistent_record {s t : Store} (h : CompileRecord.Persistent s t) : Persistent s t := by
  refine ⟨h.memory,h.inputHead,h.randomCursor,h.output,?_⟩
  intro j hj hn
  have includeR : CompileRecord.work ⊆ work := by decide
  exact h.tapes j hj (fun he => hn (includeR he))

theorem persistent_finish {s t : Store} (h : SourceCircuit.Frame RowSum.outputWork s.val t.val)
    (hm : t.val.memory = s.val.memory) : Persistent s t := by
  refine ⟨hm,h.inputHead,h.randomCursor,h.output,?_⟩
  intro j hj hn
  have includeR : RowSum.outputWork ⊆ work := by decide
  exact h.tapes j hj (fun he => hn (includeR he))

set_option maxRecDepth 16384 in
theorem finish_executes (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (d : Data) (s : Store) (hc : clock.length = width)
    (hr : Ready clock precision d s) (hv : Shape width d)
    (hroom : addressValue d.next+1+d.terms.length < 2^width) :
    ∃ cost t, cost ≤ FinalizeRow.costBound d.terms.length width d.counter.length ∧
      Executes input tape FinalizeRow.code cost s t ∧ Ready clock precision (finish d) t ∧
      Persistent s t ∧ (∀ j, j ∉ RowSum.outputWork → (j=4 ∨ 10≤j) → t.val.tapes j = s.val.tapes j) := by
  obtain ⟨counterOrigin,hcounter⟩ := hr.counter
  obtain ⟨cost,t,hcost,et,td,_,t106,t103,tm,tf⟩ := FinalizeRow.executes input tape width
    d.next d.gates clock d.counter d.outputs d.terms counterOrigin s hv.nextLength hc hv.termLength
    hroom hv.counterValue hr.scratch hr.blank94 hr.blank96 hr.blank99 hr.next hr.gates hr.blank103
    hr.terms hr.outputs hcounter hr.clock
  have zeroCount : BankArray.Word t.val 106 [] := by
    obtain ⟨o,ho⟩ := t106
    exact ⟨o,by simpa using ho⟩
  refine ⟨cost,t,hcost,et,⟨td.scratch,
    RationalAccumulator.blank_of_eq (et.protectsTape 7 (by decide)) hr.blank7,
    td.blank94,td.blank96,td.blank99,t103,td.next,td.gates,td.terms,td.outputs,zeroCount,td.clock,
    BankArray.word_of_eq (tf.tapes 82 (by omega) (by decide)) hr.power,
    (tf.tapes 10 (by omega) (by decide)).trans hr.blank10,
    (tf.tapes 15 (by omega) (by decide)).trans hr.blank15,
    (tf.tapes 16 (by omega) (by decide)).trans hr.blank16,
    RationalAccumulator.blank_of_eq (tf.tapes 83 (by omega) (by decide)) hr.blank83⟩,
    persistent_finish tf tm,fun j hj hn => tf.tapes j hn hj⟩

set_option maxRecDepth 16384 in
theorem term_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (r : AllocationPass.Record n) (d : Data)
    (preceding suffix beforeLeaves leafSuffix : List Bool) (s : Store)
    (hc : clock.length = width) (hp : r.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Shape width d)
    (hleaves : r.bits.count true ≤ d.leaves.length)
    (hroom : addressValue d.next + termGateCost r < 2^width)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (r.wire ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t, cost ≤ CompileRecord.bound r.row r.column.val precision width d.counter.length ∧
      Executes input tape CompileRecord.code cost s t ∧ Ready clock precision (term r d) t ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor (preceding ++ (r.wire ++ suffix))
        (preceding.length+r.wire.length) ∧
      t.val.tapes 98 = Increment.cursor
        (beforeLeaves ++ (d.leaves.take (r.bits.count true)).flatten)
        ((d.leaves.drop (r.bits.count true)).flatten ++ leafSuffix) 0 ∧ Persistent s t ∧
      (∀ j, j ∉ CompileRecord.work → (j=4 ∨ 10≤j) → t.val.tapes j = s.val.tapes j) := by
  obtain ⟨origin,h83⟩ := hr.blank83
  obtain ⟨powerOrigin,h82⟩ := hr.power
  have splitLeaves : d.leaves.flatten = (d.leaves.take (r.bits.count true)).flatten ++
      (d.leaves.drop (r.bits.count true)).flatten := by
    rw [← List.flatten_append,List.take_append_drop]
  obtain ⟨cost,t,hcost,et,td,_,t10,t15,t16,t83,t106,t98,t85,tf⟩ :=
    CompileRecord.executes input tape width r.row r.column.val clock r.bits d.next d.gates
      beforeLeaves ((d.leaves.drop (r.bits.count true)).flatten ++ leafSuffix)
      preceding suffix d.counter (d.leaves.take (r.bits.count true)) d.terms
      r.negative origin powerOrigin s hc hv.nextLength
      (by simp [List.length_take,Nat.min_eq_left hleaves])
      (fun word hw => hv.leafLength word (List.mem_of_mem_take hw))
      (by simpa [termGateCost,Nat.add_assoc] using hroom)
      hr.scratch hr.blank94 hr.blank96 hr.blank99 hr.next hr.gates hr.clock hr.blank103
      (by simpa [splitLeaves,List.append_assoc] using h98) hr.terms hr.counter
      hr.blank10 hr.blank15 hr.blank16 h83 (by simpa [hp] using h82) h85
  have ready : Ready clock precision (term r d) t :=
    ⟨td.scratch,RationalAccumulator.blank_of_eq (et.protectsTape 7 (by decide)) hr.blank7,
      td.blank94,td.blank96,td.blank99,td.blank103,td.next,td.gates,td.terms,
      (tf.tapes 105 (by omega) (by decide)).trans hr.outputs,t106,td.clock,
      BankArray.word_of_eq (tf.tapes 82 (by omega) (by decide)) ⟨powerOrigin,h82⟩,
      t10,t15,t16,⟨origin+r.bits.length,t83⟩⟩
  exact ⟨cost,t,by simpa [hp] using hcost,et,ready,t85,t98,persistent_record tf,
    fun j hj hn => tf.tapes j hn hj⟩

end Maxwell.Cost.SourceCircuit.ArithmeticPass
