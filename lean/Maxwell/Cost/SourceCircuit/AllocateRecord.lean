import Maxwell.Cost.SourceCircuit.AllocationScan
import Maxwell.Cost.SourceCircuit.SelectColumn
import Maxwell.Cost.SourceCircuit.RecordCleanup
import Maxwell.Cost.NormalizedRecordParser

namespace Maxwell.Cost.SourceCircuit.AllocateRecord
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq NormalizedRecordParser.code
  (.seq SelectColumn.code (.seq allocationScanCode RecordCleanup.code))

def work : Finset ℕ := {15,16,37,83,85,91,94,95,96,97,98}

structure Persistent (s t : Store) : Prop where
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j

def bound (row column : ℕ) (bits width base clock : List Bool) : ℕ :=
  40*row.bits.length+49*column.bits.length+24*bits.length+98*clock.length+191+
    bits.length*(occurrenceCost width (FixedWidth.bits clock.length column.bits) base clock+8)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (row : ℕ) (column : Fin n) (negative : Bool) (bits preceding suffix : List Bool)
    (width index base clock : List Bool) (clockOrigin outputOrigin : ℤ)
    (d : AllocationData n) (s : Store)
    (hw : 0 < width.length) (hclock : clock.length = addressValue width)
    (hp : 0 < clock.length) (hfit : column.val.bits.length ≤ clock.length)
    (hi : index.length = clock.length)
    (hr : AllocationReady width index base clock d s)
    (hv : AllocationValid (addressValue base) (addressValue width) bits d)
    (h10 : s.val.tapes 10 = BitTape.blank) (h15 : s.val.tapes 15 = BitTape.blank)
    (h16 : s.val.tapes 16 = BitTape.blank) (h37 : Blank s.val 37)
    (h83 : s.val.tapes 83 = {BitTape.blank with head := outputOrigin})
    (h82 : s.val.tapes 82 = BitTape.shifted (2^bits.length).bits clockOrigin)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (normalizedRecord row column.val negative bits ++ suffix)) preceding.length) :
    ∃ cost t, cost ≤ bound row column.val bits width base clock ∧ Executes input tape code cost s t ∧
      AllocationReady width (FixedWidth.bits clock.length column.val.bits) base clock
        (ScanBits.fold (AllocationData.split (addressValue base) (addressValue width) column) bits d) t ∧
      AllocationValid (addressValue base) (addressValue width) []
        (ScanBits.fold (AllocationData.split (addressValue base) (addressValue width) column) bits d) ∧
      t.val.tapes 10 = BitTape.blank ∧ t.val.tapes 15 = BitTape.blank ∧
      t.val.tapes 16 = BitTape.blank ∧ Blank t.val 37 ∧
      t.val.tapes 83 = {BitTape.blank with head := outputOrigin} ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor
        (preceding ++ (normalizedRecord row column.val negative bits ++ suffix))
        (preceding.length+(normalizedRecord row column.val negative bits).length) ∧ Persistent s t := by
  obtain ⟨pc,p,ep,hpc,p15,p16,_,p83,p85,pi,pf⟩ := NormalizedRecordParser.executes input tape
    row column.val negative bits preceding suffix clockOrigin outputOrigin s h85 h10 h15 h16 h83 h82
  have pk (j : ℕ) (hj : j ∉ NormalizedRecordParser.work) : p.val.tapes j = s.val.tapes j := pf.tapes j hj
  have pr : AllocationReady width index base clock d p :=
    ⟨scratch_of_tapes hr.scratch (fun j hj => pk j (by simp [NormalizedRecordParser.work]; omega)),
      RationalAccumulator.blank_of_eq (pk 7 (by decide)) hr.blank7,
      RationalAccumulator.blank_of_eq (pk 94 (by decide)) hr.blank94,
      RationalAccumulator.blank_of_eq (pk 96 (by decide)) hr.blank96,
      BankArray.word_of_eq (pk 90 (by decide)) hr.width,
      BankArray.word_of_eq (pk 91 (by decide)) hr.index,
      BankArray.word_of_eq (pk 92 (by decide)) hr.base,
      BankArray.word_of_eq (pk 93 (by decide)) hr.clock,
      BankArray.word_of_eq (pk 95 (by decide)) hr.next,
      (pk 97 (by decide)).trans hr.gates,(pk 98 (by decide)).trans hr.leaves,
      pf.memory.trans hr.memory⟩
  obtain ⟨sc,c,hsc,ec,ci,c16,c37,c7,cs,cm,cf⟩ := SelectColumn.executes input tape column.val
    clock index p hp hfit hi pr.scratch pr.blank7
    (RationalAccumulator.blank_of_eq (pk 37 (by decide)) h37) p16 pr.clock pr.index
  have cr : AllocationReady width (FixedWidth.bits clock.length column.val.bits) base clock d c :=
    ⟨cs,c7,RationalAccumulator.blank_of_eq (cf.tapes 94 (by omega) (by decide)) pr.blank94,
      RationalAccumulator.blank_of_eq (cf.tapes 96 (by omega) (by decide)) pr.blank96,
      BankArray.word_of_eq (cf.tapes 90 (by omega) (by decide)) pr.width,ci,
      BankArray.word_of_eq (cf.tapes 92 (by omega) (by decide)) pr.base,
      BankArray.word_of_eq (cf.tapes 93 (by omega) (by decide)) pr.clock,
      BankArray.word_of_eq (cf.tapes 95 (by omega) (by decide)) pr.next,
      (cf.tapes 97 (by omega) (by decide)).trans pr.gates,
      (cf.tapes 98 (by omega) (by decide)).trans pr.leaves,cm.trans pr.memory⟩
  have cindex : addressValue (FixedWidth.bits clock.length column.val.bits) = column.val := by
    rw [FixedWidth.bits_value _ _ hfit,addressValue_bits]
  obtain ⟨ac,a,hac,ea,ar,av,a83,af⟩ := allocationScan_executes input tape width
    (FixedWidth.bits clock.length column.val.bits) base clock column hw cindex hclock bits outputOrigin d c cr hv
    ((cf.tapes 83 (by omega) (by decide)).trans p83)
  obtain ⟨t,et,tt,tm,tf⟩ := RecordCleanup.executes input tape row.bits column.val.bits bits outputOrigin a
    ((af.tapes 15 (by omega) (by decide)).trans ((cf.tapes 15 (by omega) (by decide)).trans p15))
    ((af.tapes 16 (by omega) (by decide)).trans c16) a83
  have tk (j : ℕ) (hj : j ∉ RecordCleanup.work) : t.val.tapes j = a.val.tapes j := by
    simp only [RecordCleanup.work,Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    simp [tt,hj.1,hj.2.1,hj.2.2]
  have tr : AllocationReady width (FixedWidth.bits clock.length column.val.bits) base clock _ t :=
    ⟨scratch_of_tapes ar.scratch (fun j hj => tk j (by simp [RecordCleanup.work]; omega)),
      RationalAccumulator.blank_of_eq (tk 7 (by decide)) ar.blank7,
      RationalAccumulator.blank_of_eq (tk 94 (by decide)) ar.blank94,
      RationalAccumulator.blank_of_eq (tk 96 (by decide)) ar.blank96,
      BankArray.word_of_eq (tk 90 (by decide)) ar.width,
      BankArray.word_of_eq (tk 91 (by decide)) ar.index,
      BankArray.word_of_eq (tk 92 (by decide)) ar.base,
      BankArray.word_of_eq (tk 93 (by decide)) ar.clock,
      BankArray.word_of_eq (tk 95 (by decide)) ar.next,
      (tk 97 (by decide)).trans ar.gates,(tk 98 (by decide)).trans ar.leaves,tm.trans ar.memory⟩
  have keep (j : ℕ) (hj : j = 4 ∨ 10 ≤ j) (hn : j ∉ work) : t.val.tapes j = s.val.tapes j := by
    have hlist : j ≠ 15 ∧ j ≠ 16 ∧ j ≠ 37 ∧ j ≠ 83 ∧ j ≠ 85 ∧ j ≠ 91 ∧
      j ≠ 94 ∧ j ≠ 95 ∧ j ≠ 96 ∧ j ≠ 97 ∧ j ≠ 98 := by simpa [work] using hn
    rcases hlist with ⟨h15,h16,h37,h83,h85,h91,h94,h95,h96,h97,h98⟩
    exact (tk j (by simp [RecordCleanup.work,h15,h16,h83])).trans
      ((af.tapes j hj (by simp [allocationScanWork,h83,h94,h95,h96,h97,h98])).trans
        ((cf.tapes j hj (by simp [SelectColumn.work,h16,h37,h91])).trans
          (pk j (by simp [NormalizedRecordParser.work,h15,h16,h83,h85]))))
  refine ⟨pc+(sc+(ac+(6*row.bits.length+11*column.val.bits.length+6*bits.length+22))),t,?_,
    ep.seq (ec.seq (ea.seq et)),tr,av,(keep 10 (by omega) (by decide)).trans h10,
    by simp [tt],by simp [tt],
    RationalAccumulator.blank_of_eq ((tk 37 (by decide)).trans (af.tapes 37 (by omega) (by decide))) c37,
    by simp [tt],
    (tk 85 (by decide)).trans ((af.tapes 85 (by omega) (by decide)).trans
      ((cf.tapes 85 (by omega) (by decide)).trans p85)),
    ⟨tf.inputHead.trans (af.inputHead.trans (cf.inputHead.trans pi)),
      tf.randomCursor.trans (af.randomCursor.trans (cf.randomCursor.trans pf.randomCursor)),
      tf.output.trans (af.output.trans (cf.output.trans pf.output)),keep⟩⟩
  unfold bound
  omega

end Maxwell.Cost.SourceCircuit.AllocateRecord
