import Maxwell.Cost.SourceCircuit.ArithmeticPass

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass
open Structured

/-- Consume the first nonempty-row marker, then run the uniform row loop. -/
def code : Code := .seq (CountedShifted.test 100) (.seq firstCode tailCode)
def program : BitRAM := code.compile

def result {n : ℕ} (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data) : Data :=
  loop records flags (term r d)

def costBound {n : ℕ} (precision width counterLength : ℕ) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data) : ℕ :=
  13*counterLength+19 + CompileRecord.bound r.row r.column.val precision width width +
    tailBound precision width counterLength records flags (term r d)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (r : AllocationPass.Record n) (records : List (AllocationPass.Record n))
    (marker : Bool) (flags : List Bool) (d : Data)
    (preceding suffix beforeLeaves leafSuffix beforeMarkers followingMarkers counter : List Bool)
    (counterOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hp : ∀ q ∈ r::records, q.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Valid width (r::records) (false::flags) d)
    (hcount : addressValue counter = records.length+1)
    (h100 : s.val.tapes 100 = BitTape.shifted counter counterOrigin)
    (h24 : s.val.tapes 24 = Increment.cursor beforeMarkers (marker::(flags ++ followingMarkers)) 0)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (AllocationPass.wire (r::records) ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t finalCounter,
      cost ≤ costBound precision width counter.length r records flags d ∧
      Executes input tape code cost s t ∧ Ready clock precision (result r records flags d) t ∧
      Finished width (result r records flags d) ∧
      t.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧ finalCounter.length = counter.length ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (AllocationPass.wire (r::records) ++ suffix))
        (preceding.length+(AllocationPass.wire (r::records)).length) ∧
      t.val.tapes 98 = Increment.cursor (beforeLeaves ++ d.leaves.flatten) leafSuffix 0 ∧
      t.val.tapes 24 = Increment.cursor (beforeMarkers ++ (marker::flags)) followingMarkers 0 ∧
      Persistent s t := by
  obtain ⟨tested,etest,t100,_,tf⟩ :=
    CountedShifted.test_executes 100 counterOrigin input tape s counter h100
  have decrease : addressValue (subtractBit true counter) = records.length := by
    rw [subtractBit_pred counter (by omega),hcount]
    omega
  have vt : Valid width records flags (term r d) := valid_body false r records flags d hv
  have enough : r.bits.count true ≤ d.leaves.length := by
    have hh := hv.leavesCount
    simp only [AllocationPass.occurrences,List.map_cons,List.sum_cons] at hh
    omega
  have room : addressValue d.next+termGateCost r < 2^width := by
    have hh := vt.room
    rw [term_next] at hh
    omega
  obtain ⟨fc,m,hfc,ef,mr,m85,m98,m24,mf,m100⟩ :=
    first_executes input tape clock precision width marker r d preceding
      (AllocationPass.wire records ++ suffix) beforeLeaves leafSuffix beforeMarkers
      (flags ++ followingMarkers) tested hc (hp r (by simp)) (hr.count tf) hv.shape enough room
      ((tf.2.2.2.2.2.1 24 (by omega)).trans h24)
      (by simpa [AllocationPass.wire,List.append_assoc] using (tf.2.2.2.2.2.1 85 (by omega)).trans h85)
      ((tf.2.2.2.2.2.1 98 (by omega)).trans h98)
  obtain ⟨tc,t,finalCounter,htc,et,tr,tv,t100,tl,t85,t98,t24,ft⟩ :=
    tail_executes input tape clock precision width records flags (term r d)
      (preceding ++ r.wire) suffix (beforeLeaves ++ (d.leaves.take (r.bits.count true)).flatten)
      leafSuffix (beforeMarkers ++ [marker]) followingMarkers (subtractBit true counter) counterOrigin m
      hc (fun q hq => hp q (by simp [hq])) mr vt decrease (m100.trans t100) m24
      (by simpa [List.append_assoc] using m85) m98
  refine ⟨13*counter.length+14+(fc+tc),t,finalCounter,?_,etest.seq (ef.seq et),tr,tv,t100,
    tl.trans (subtractBit_length true counter),?_,?_,?_,(persistent_count tf).trans (mf.trans ft)⟩
  · simp only [subtractBit_length] at htc
    unfold costBound
    omega
  · simpa [AllocationPass.wire,List.append_assoc,Nat.add_assoc,Int.add_assoc] using t85
  · have splitLeaves : (d.leaves.take (r.bits.count true)).flatten ++
        (d.leaves.drop (r.bits.count true)).flatten = d.leaves.flatten := by
      rw [← List.flatten_append,List.take_append_drop]
    simpa [term,List.append_assoc,splitLeaves] using t98
  · simpa [List.append_assoc] using t24

set_option maxRecDepth 16384 in
theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (r : AllocationPass.Record n) (records : List (AllocationPass.Record n))
    (marker : Bool) (flags : List Bool) (d : Data)
    (preceding suffix beforeLeaves leafSuffix beforeMarkers followingMarkers counter : List Bool)
    (counterOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hp : ∀ q ∈ r::records, q.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Valid width (r::records) (false::flags) d)
    (hcount : addressValue counter = records.length+1)
    (h100 : s.val.tapes 100 = BitTape.shifted counter counterOrigin)
    (h24 : s.val.tapes 24 = Increment.cursor beforeMarkers (marker::(flags ++ followingMarkers)) 0)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (AllocationPass.wire (r::records) ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t finalCounter,
      (runPriced (program.next input tape)
        (costBound precision width counter.length r records flags d+1) s.val).finished =
          some (t.place code.size) ∧
      (runPriced (program.next input tape)
        (costBound precision width counter.length r records flags d+1) s.val).instructions = cost ∧
      cost ≤ costBound precision width counter.length r records flags d ∧
      Ready clock precision (result r records flags d) t ∧ Finished width (result r records flags d) ∧
      t.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧ finalCounter.length = counter.length ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (AllocationPass.wire (r::records) ++ suffix))
        (preceding.length+(AllocationPass.wire (r::records)).length) ∧
      t.val.tapes 98 = Increment.cursor (beforeLeaves ++ d.leaves.flatten) leafSuffix 0 ∧
      t.val.tapes 24 = Increment.cursor (beforeMarkers ++ (marker::flags)) followingMarkers 0 ∧
      Persistent s t := by
  obtain ⟨cost,t,finalCounter,hcost,et,tr,tv,t100,tl,t85,t98,t24,tf⟩ := executes input tape clock
    precision width r records marker flags d preceding suffix beforeLeaves leafSuffix beforeMarkers
    followingMarkers counter counterOrigin s hc hp hr hv hcount h100 h24 h85 h98
  obtain ⟨finished,charged⟩ := et.compiled_run
    (costBound precision width counter.length r records flags d+1) (by omega)
  exact ⟨cost,t,finalCounter,finished,charged,hcost,tr,tv,t100,tl,t85,t98,t24,tf⟩

end Maxwell.Cost.SourceCircuit.ArithmeticPass
