import Maxwell.Cost.SourceCircuit.AllocationPassData

namespace Maxwell.Cost.SourceCircuit.AllocationPass
open Structured

def code : Code := CountedShifted.code 100 AllocateRecord.code
def program : BitRAM := code.compile

def costBound {n : ℕ} (records : List (Record n)) (width base clock counter : List Bool) : ℕ :=
  (records.length+1) * (13*counter.length+15) +
    records.length * maximumCost width base clock records

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (records : List (Record n)) (preceding suffix width index base clock counter : List Bool)
    (precision : ℕ) (powerOrigin outputOrigin counterOrigin : ℤ)
    (d : AllocationData n) (s : Store)
    (hw : 0 < width.length) (hclock : clock.length = addressValue width) (hp : 0 < clock.length)
    (hfit : ∀ r ∈ records, r.column.val.bits.length ≤ clock.length)
    (hprecision : ∀ r ∈ records, r.bits.length = precision)
    (hcount : addressValue counter = records.length)
    (hcounter : s.val.tapes 100 = BitTape.shifted counter counterOrigin)
    (ready : Ready width index base clock precision powerOrigin outputOrigin d s)
    (valid : Valid (addressValue base) (addressValue width) records d)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (wire records ++ suffix)) preceding.length) :
    ∃ cost, ∃ t : Store, ∃ finalCounter : List Bool,
      cost ≤ costBound records width base clock counter ∧ Executes input tape code cost s t ∧
      Ready width (finalIndex clock.length records index) base clock precision powerOrigin outputOrigin
        (allocate (addressValue base) (addressValue width) records d) t ∧
      Valid (addressValue base) (addressValue width) []
        (allocate (addressValue base) (addressValue width) records d) ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (wire records ++ suffix)) (preceding.length+(wire records).length) ∧
      t.val.tapes 100 = BitTape.shifted finalCounter counterOrigin ∧
      finalCounter.length = counter.length ∧ Persistent s t := by
  let full := preceding ++ wire records
  let inv : ℕ → Store → Prop := fun remaining u =>
    ∃ pending : List (Record n), ∃ before idx : List Bool, ∃ current : AllocationData n,
      pending.length = remaining ∧ before ++ wire pending = full ∧
      (∀ r ∈ pending, r ∈ records) ∧
      allocate (addressValue base) (addressValue width) pending current =
        allocate (addressValue base) (addressValue width) records d ∧
      finalIndex clock.length pending idx = finalIndex clock.length records index ∧
      Ready width idx base clock precision powerOrigin outputOrigin current u ∧
      Valid (addressValue base) (addressValue width) pending current ∧
      u.val.tapes 85 = NormalizedRecordParser.cursor (full ++ suffix) before.length ∧ Persistent s u
  have stable : ∀ remaining u v, Counted.Frame 100 u v → inv remaining u → inv remaining v := by
    rintro remaining u v hf ⟨pending, before, idx, current, hn, hfull, members, ha, hi, hr, hv, hc, frame⟩
    exact ⟨pending, before, idx, current, hn, hfull, members, ha, hi, hr.count hf, hv,
      (hf.2.2.2.2.2.1 85 (by omega)).trans hc, frame.trans (persistent_count hf)⟩
  have correct : ∀ remaining xs u, inv (remaining+1) u →
      u.val.tapes 100 = BitTape.shifted xs counterOrigin → addressValue xs = remaining →
      ∃ cost v, Executes input tape AllocateRecord.code cost u v ∧ inv remaining v ∧
        v.val.tapes 100 = BitTape.shifted xs counterOrigin ∧
        cost ≤ maximumCost width base clock records := by
    rintro remaining xs u ⟨pending, before, idx, current, hn, hfull, members, ha, hi, hr, hv, hc, frame⟩ hcounter _
    cases pending with
    | nil => simp at hn
    | cons r rest =>
      have member : r ∈ records := members r (by simp)
      have inputWire : before ++ (r.wire ++ (wire rest ++ suffix)) = full ++ suffix := by
        simpa [wire, List.append_assoc] using congrArg (fun bs => bs ++ suffix) hfull
      have cursor : u.val.tapes 85 = NormalizedRecordParser.cursor
          (before ++ (normalizedRecord r.row r.column.val r.negative r.bits ++ (wire rest ++ suffix)))
          before.length := by
        change u.val.tapes 85 = NormalizedRecordParser.cursor
          (before ++ (r.wire ++ (wire rest ++ suffix))) before.length
        rw [inputWire]
        exact hc
      obtain ⟨cost, v, hcost, ev, vr, vv, v10, v15, v16, v37, v83, v85, vf⟩ :=
        AllocateRecord.executes input tape r.row r.column r.negative r.bits before (wire rest ++ suffix)
          width idx base clock powerOrigin outputOrigin current u hw hclock hp (hfit r member)
          hr.indexLength hr.allocation hv.head hr.blank10 hr.blank15 hr.blank16 hr.blank37 hr.blank83
          (by simpa [hprecision r member] using hr.power) cursor
      have nextReady : Ready width (FixedWidth.bits clock.length r.column.val.bits) base clock
          precision powerOrigin outputOrigin (applyRecord (addressValue base) (addressValue width) r current) v :=
        ⟨vr, FixedWidth.bits_length _ _, v10, v15, v16, v37, v83,
          (vf.tapes 82 (by omega) (by decide)).trans hr.power⟩
      refine ⟨cost, v, ev, ⟨rest, before ++ r.wire,
        FixedWidth.bits clock.length r.column.val.bits,
        applyRecord (addressValue base) (addressValue width) r current,
        (by simpa using hn), ?_, (fun q hq => members q (by simp [hq])), ha, hi, nextReady,
        hv.tail vv, ?_, frame.trans (persistent_record vf)⟩,
        (vf.tapes 100 (by omega) (by decide)).trans hcounter,
        hcost.trans (recordCost_le width base clock records r member)⟩
      · simpa [wire, List.append_assoc] using hfull
      · change v.val.tapes 85 = NormalizedRecordParser.cursor
          (before ++ (r.wire ++ (wire rest ++ suffix))) ((before.length : ℤ) + r.wire.length) at v85
        rw [inputWire] at v85
        simpa only [List.length_append, Nat.cast_add] using v85
  have initial : inv records.length s :=
    ⟨records, preceding, index, d, rfl, rfl, fun _ h => h, rfl, rfl, ready, valid,
      (by simpa [full, List.append_assoc] using h85), Persistent.refl s⟩
  obtain ⟨cost, t, finalCounter, he, hi, hct, hlen, _, hcost⟩ :=
    CountedShifted.executes 100 counterOrigin AllocateRecord.code input tape inv
      (fun _ => maximumCost width base clock records) stable correct records.length counter s
      hcount hcounter initial
  obtain ⟨pending, before, idx, current, hn, hfull, _, ha, hidx, hr, hv, hc, frame⟩ := hi
  have empty : pending = [] := by simpa using hn
  subst pending
  have dataEq : current = allocate (addressValue base) (addressValue width) records d := ha
  have indexEq : idx = finalIndex clock.length records index := hidx
  have beforeEq : before = full := by simpa [wire] using hfull
  refine ⟨cost, t, finalCounter, ?_, he, ?_, ?_, ?_, hct, hlen, frame⟩
  · simpa [costBound] using hcost
  · simpa only [dataEq, indexEq] using hr
  · simpa only [dataEq] using hv
  · simpa [beforeEq, full, List.append_assoc] using hc

theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (records : List (Record n)) (preceding suffix width index base clock counter : List Bool)
    (precision : ℕ) (powerOrigin outputOrigin counterOrigin : ℤ)
    (d : AllocationData n) (s : Store)
    (hw : 0 < width.length) (hclock : clock.length = addressValue width) (hp : 0 < clock.length)
    (hfit : ∀ r ∈ records, r.column.val.bits.length ≤ clock.length)
    (hprecision : ∀ r ∈ records, r.bits.length = precision)
    (hcount : addressValue counter = records.length)
    (hcounter : s.val.tapes 100 = BitTape.shifted counter counterOrigin)
    (ready : Ready width index base clock precision powerOrigin outputOrigin d s)
    (valid : Valid (addressValue base) (addressValue width) records d)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (wire records ++ suffix)) preceding.length) :
    ∃ cost, ∃ t : Store,
      (runPriced (program.next input tape) (costBound records width base clock counter+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (program.next input tape) (costBound records width base clock counter+1) s.val).instructions = cost ∧
      cost ≤ costBound records width base clock counter ∧
      Ready width (finalIndex clock.length records index) base clock precision powerOrigin outputOrigin
        (allocate (addressValue base) (addressValue width) records d) t ∧
      Valid (addressValue base) (addressValue width) []
        (allocate (addressValue base) (addressValue width) records d) ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (wire records ++ suffix)) (preceding.length+(wire records).length) ∧ Persistent s t := by
  obtain ⟨cost, t, _, hcost, he, hr, hv, h85, _, _, hf⟩ := executes input tape records
    preceding suffix width index base clock counter precision powerOrigin outputOrigin counterOrigin d s
    hw hclock hp hfit hprecision hcount hcounter ready valid h85
  obtain ⟨finished, charged⟩ := he.compiled_run (costBound records width base clock counter+1) (by omega)
  exact ⟨cost, t, finished, charged, hcost, hr, hv, h85, hf⟩

end Maxwell.Cost.SourceCircuit.AllocationPass
