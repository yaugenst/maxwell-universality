import Maxwell.Cost.SourceCircuit.ArithmeticStep

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass
open Structured

/-- One finite counted program, followed by the final row reduction. -/
def tailCode : Code := .seq (CountedShifted.code 100 stepCode) FinalizeRow.code

def recordCosts {n : ℕ} (precision width : ℕ) (records : List (AllocationPass.Record n)) : ℕ :=
  (records.map fun r => CompileRecord.bound r.row r.column.val precision width width + 7).sum

def tailBound {n : ℕ} (precision width counterLength : ℕ)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data) : ℕ :=
  (records.length+1)*(13*counterLength+15) + recordCosts precision width records +
    rowCost width records flags d

theorem body_leaves {n : ℕ} (boundary : Bool) (r : AllocationPass.Record n) (d : Data) :
    (body boundary r d).leaves = d.leaves.drop (r.bits.count true) := by
  cases boundary <;> rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1500000 in
theorem tail_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data)
    (preceding suffix beforeLeaves leafSuffix beforeMarkers followingMarkers counter : List Bool)
    (counterOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hp : ∀ r ∈ records, r.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Valid width records flags d)
    (hcount : addressValue counter = records.length)
    (h100 : s.val.tapes 100 = BitTape.shifted counter counterOrigin)
    (h24 : s.val.tapes 24 = Increment.cursor beforeMarkers (flags ++ followingMarkers) 0)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (AllocationPass.wire records ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t finalCounter,
      cost ≤ tailBound precision width counter.length records flags d ∧
      Executes input tape tailCode cost s t ∧ Ready clock precision (loop records flags d) t ∧
      Finished width (loop records flags d) ∧
      t.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧ finalCounter.length = counter.length ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (AllocationPass.wire records ++ suffix))
        (preceding.length+(AllocationPass.wire records).length) ∧
      t.val.tapes 98 = Increment.cursor (beforeLeaves ++ d.leaves.flatten) leafSuffix 0 ∧
      t.val.tapes 24 = Increment.cursor (beforeMarkers ++ flags) followingMarkers 0 ∧
      Persistent s t := by
  induction records generalizing flags d preceding beforeLeaves beforeMarkers counter s with
  | nil =>
    have hf : flags = [] := by simpa using hv.flagsLength
    subst flags
    obtain ⟨tested,etest,t100,tzero,tf⟩ :=
      CountedShifted.test_executes 100 counterOrigin input tape s counter h100
    have hfalse : tested.val.registers 29 = false := tzero.mpr hcount
    have room : addressValue d.next+1+d.terms.length < 2^width := by
      have hh := hv.room
      simpa [reserve,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
    obtain ⟨cost,t,hcost,et,tr,ft,keep⟩ :=
      finish_executes input tape clock precision width d tested hc (hr.count tf) hv.shape room
    have empty : d.leaves = [] := by
      have hh := hv.leavesCount
      simpa [AllocationPass.occurrences] using hh
    refine ⟨13*counter.length+14+1+cost,t,subtractBit true counter,?_,
      (etest.seq (.done hfalse)).seq et,tr,valid_finish d hv,
      (keep 100 (by decide) (by omega)).trans t100,subtractBit_length true counter,?_,?_,?_,
      (persistent_count tf).trans ft⟩
    · simpa [tailBound,recordCosts,rowCost,Nat.add_assoc] using Nat.add_le_add_left hcost (13*counter.length+15)
    · simpa [AllocationPass.wire] using
        (keep 85 (by decide) (by omega)).trans ((tf.2.2.2.2.2.1 85 (by omega)).trans h85)
    · simpa [empty] using
        (keep 98 (by decide) (by omega)).trans ((tf.2.2.2.2.2.1 98 (by omega)).trans h98)
    · simpa using (keep 24 (by decide) (by omega)).trans ((tf.2.2.2.2.2.1 24 (by omega)).trans h24)
  | cons r records ih =>
    cases flags with
    | nil => have hh := hv.flagsLength; simp at hh
    | cons boundary flags =>
      obtain ⟨tested,etest,t100,tzero,tf⟩ :=
        CountedShifted.test_executes 100 counterOrigin input tape s counter h100
      have hpositive : 0 < addressValue counter := by simpa only [List.length_cons] using hcount ▸ Nat.zero_lt_succ records.length
      have decrease : addressValue (subtractBit true counter) = records.length := by
        rw [subtractBit_pred counter hpositive,hcount,List.length_cons]
        omega
      have htrue : tested.val.registers 29 = true := by
        cases hb : tested.val.registers 29 with
        | true => rfl
        | false => have hh := tzero.mp hb; omega
      obtain ⟨bc,m,hbc,eb,mr,mv,m85,m98,m24,mf,m100⟩ :=
        step_executes input tape clock precision width boundary r records flags d preceding
          (AllocationPass.wire records ++ suffix) beforeLeaves leafSuffix beforeMarkers
          (flags ++ followingMarkers) tested hc (hp r (by simp)) (hr.count tf) hv
          (by simpa using (tf.2.2.2.2.2.1 24 (by omega)).trans h24)
          (by simpa [AllocationPass.wire,List.append_assoc] using (tf.2.2.2.2.2.1 85 (by omega)).trans h85)
          ((tf.2.2.2.2.2.1 98 (by omega)).trans h98)
      obtain ⟨rc,t,finalCounter,hrc,er,tr,tv,t100,tl,t85,t98,t24,ft⟩ :=
        ih flags (body boundary r d) (preceding ++ r.wire)
          (beforeLeaves ++ (d.leaves.take (r.bits.count true)).flatten)
          (beforeMarkers ++ [boundary]) (subtractBit true counter) m
          (fun q hq => hp q (by simp [hq])) mr mv decrease (m100.trans t100)
          m24
          (by simpa [List.append_assoc] using m85)
          (by simpa [body_leaves] using m98)
      change Executes input tape (.seq (.seq (CountedShifted.test 100)
        (.loop 29 (.seq stepCode (CountedShifted.test 100)))) FinalizeRow.code) rc m t at er
      cases er with
      | seq eloop efinish =>
        cases eloop with
        | seq restTest restLoop =>
          refine ⟨_,t,finalCounter,?_,
            (etest.seq (.more htrue (eb.seq restTest) restLoop)).seq efinish,tr,tv,t100,
            tl.trans (subtractBit_length true counter),?_,?_,?_,
            (persistent_count tf).trans (mf.trans ft)⟩
          · simp only [tailBound,recordCosts,List.map_cons,List.sum_cons,List.length_cons,
              rowCost,subtractBit_length] at hrc ⊢
            nlinarith
          · simpa [AllocationPass.wire,List.append_assoc,Nat.add_assoc,Int.add_assoc] using t85
          · have splitLeaves : (d.leaves.take (r.bits.count true)).flatten ++
                (d.leaves.drop (r.bits.count true)).flatten = d.leaves.flatten := by
              rw [← List.flatten_append,List.take_append_drop]
            simpa [body_leaves,List.append_assoc,splitLeaves] using t98
          · simpa [List.append_assoc] using t24

theorem tailBound_linear {n : ℕ} (precision width counterLength : ℕ)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data)
    (hv : Valid width records flags d) :
    tailBound precision width counterLength records flags d ≤
      (records.length+1)*(13*counterLength+15) + recordCosts precision width records +
        (d.terms.length+records.length)*(101*width+119)+(flags.count true+1)*(75*width+103) := by
  have h := rowCost_bound records flags d hv
  unfold tailBound
  omega

end Maxwell.Cost.SourceCircuit.ArithmeticPass
