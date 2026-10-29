import Maxwell.Cost.SourceCircuit.AllocateRecord
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.SourceCircuit.AllocationPass
open Structured
open RationalAccumulator (Blank)

structure Record (n : ℕ) where
  row : ℕ
  column : Fin n
  negative : Bool
  bits : List Bool
  deriving DecidableEq

def Record.wire {n : ℕ} (r : Record n) : List Bool :=
  normalizedRecord r.row r.column.val r.negative r.bits

def wire {n : ℕ} (records : List (Record n)) : List Bool := records.flatMap Record.wire

def occurrences {n : ℕ} (records : List (Record n)) : ℕ :=
  (records.map fun r => r.bits.count true).sum

def applyRecord {n : ℕ} (base width : ℕ) (r : Record n) (d : AllocationData n) : AllocationData n :=
  ScanBits.fold (AllocationData.split base width r.column) r.bits d

def allocate {n : ℕ} (base width : ℕ) : List (Record n) → AllocationData n → AllocationData n
  | [], d => d
  | r :: records, d => allocate base width records (applyRecord base width r d)

def finalIndex {n : ℕ} (width : ℕ) : List (Record n) → List Bool → List Bool
  | [], index => index
  | r :: records, _ => finalIndex width records (FixedWidth.bits width r.column.val.bits)

def recordCost {n : ℕ} (width base clock : List Bool) (r : Record n) : ℕ :=
  AllocateRecord.bound r.row r.column.val r.bits width base clock

def maximumCost {n : ℕ} (width base clock : List Bool) : List (Record n) → ℕ
  | [] => 0
  | r :: records => max (recordCost width base clock r) (maximumCost width base clock records)

theorem recordCost_le {n : ℕ} (width base clock : List Bool) (records : List (Record n))
    (r : Record n) (h : r ∈ records) : recordCost width base clock r ≤ maximumCost width base clock records := by
  induction records with
  | nil => simp at h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact (ih ht).trans (Nat.le_max_right _ _)

theorem scan_next_value {n : ℕ} (base width : ℕ) (column : Fin n)
    (bits : List Bool) (d : AllocationData n) :
    addressValue (ScanBits.fold (AllocationData.split base width column) bits d).next =
      addressValue d.next + 2 * bits.count true := by
  induction bits generalizing d with
  | nil => simp [ScanBits.fold]
  | cons bit bits ih =>
    cases bit <;> simp [ScanBits.fold, AllocationData.split, ih, Increment.bits_value,
      Nat.mul_add, Nat.add_assoc]
    omega

structure Valid {n : ℕ} (base width : ℕ) (records : List (Record n)) (d : AllocationData n) : Prop where
  array : BitArray.Represents d.memory base width d.roots
  length : d.next.length = width
  room : addressValue d.next + 2 * occurrences records < 2 ^ width

theorem Valid.head {n base width : ℕ} {r : Record n} {records : List (Record n)} {d : AllocationData n}
    (h : Valid base width (r :: records) d) : AllocationValid base width r.bits d := by
  refine ⟨h.array, h.length, ?_⟩
  have hr := h.room
  simp only [occurrences, List.map_cons, List.sum_cons] at hr
  omega

theorem Valid.tail {n base width : ℕ} {r : Record n} {records : List (Record n)} {d : AllocationData n}
    (h : Valid base width (r :: records) d)
    (result : AllocationValid base width [] (applyRecord base width r d)) :
    Valid base width records (applyRecord base width r d) := by
  refine ⟨result.array, result.length, ?_⟩
  rw [applyRecord, scan_next_value]
  have hr := h.room
  simp only [occurrences, List.map_cons, List.sum_cons] at hr ⊢
  omega

def work : Finset ℕ := insert 100 AllocateRecord.work

structure Persistent (s t : Store) : Prop where
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j

theorem Persistent.refl (s : Store) : Persistent s s := ⟨rfl,rfl,rfl,fun _ _ _ => rfl⟩
theorem Persistent.trans {s t u : Store} (h : Persistent s t) (k : Persistent t u) : Persistent s u :=
  ⟨k.inputHead.trans h.inputHead, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output, fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn)⟩

theorem persistent_count {s t : Store} (h : Counted.Frame 100 s t) : Persistent s t := by
  refine ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro j _ hj
  exact h.2.2.2.2.2.1 j (by intro he; exact hj (by simp [work, he]))

theorem persistent_record {s t : Store} (h : AllocateRecord.Persistent s t) : Persistent s t :=
  ⟨h.inputHead, h.randomCursor, h.output, fun j hj hn => h.tapes j hj (by
    intro he; exact hn (Finset.mem_insert_of_mem he))⟩

structure Ready {n : ℕ} (width index base clock : List Bool) (precision : ℕ)
    (powerOrigin outputOrigin : ℤ) (d : AllocationData n) (s : Store) : Prop where
  allocation : AllocationReady width index base clock d s
  indexLength : index.length = clock.length
  blank10 : s.val.tapes 10 = BitTape.blank
  blank15 : s.val.tapes 15 = BitTape.blank
  blank16 : s.val.tapes 16 = BitTape.blank
  blank37 : Blank s.val 37
  blank83 : s.val.tapes 83 = {BitTape.blank with head := outputOrigin}
  power : s.val.tapes 82 = BitTape.shifted (2^precision).bits powerOrigin

theorem Ready.count {n precision : ℕ} {width index base clock : List Bool}
    {powerOrigin outputOrigin : ℤ} {d : AllocationData n} {s t : Store}
    (h : Ready width index base clock precision powerOrigin outputOrigin d s)
    (f : Counted.Frame 100 s t) : Ready width index base clock precision powerOrigin outputOrigin d t := by
  let keep := f.2.2.2.2.2.1
  have hr := h.allocation
  refine ⟨⟨scratch_of_tapes hr.scratch (fun j hj => keep j (by omega)),
    RationalAccumulator.blank_of_eq (keep 7 (by omega)) hr.blank7,
    RationalAccumulator.blank_of_eq (keep 94 (by omega)) hr.blank94,
    RationalAccumulator.blank_of_eq (keep 96 (by omega)) hr.blank96,
    BankArray.word_of_eq (keep 90 (by omega)) hr.width,
    BankArray.word_of_eq (keep 91 (by omega)) hr.index,
    BankArray.word_of_eq (keep 92 (by omega)) hr.base,
    BankArray.word_of_eq (keep 93 (by omega)) hr.clock,
    BankArray.word_of_eq (keep 95 (by omega)) hr.next,
    (keep 97 (by omega)).trans hr.gates, (keep 98 (by omega)).trans hr.leaves,
    f.2.2.1.trans hr.memory⟩, h.indexLength,
    (keep 10 (by omega)).trans h.blank10, (keep 15 (by omega)).trans h.blank15,
    (keep 16 (by omega)).trans h.blank16,
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) h.blank37,
    (keep 83 (by omega)).trans h.blank83, (keep 82 (by omega)).trans h.power⟩

end Maxwell.Cost.SourceCircuit.AllocationPass
