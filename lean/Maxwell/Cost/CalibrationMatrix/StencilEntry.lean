import Maxwell.Cost.CalibrationMatrix.MaterialHeader
import Maxwell.Cost.CalibrationMatrix.TestEntry
import Maxwell.Cost.CalibrationMatrix.DirectionSelect
import Maxwell.Cost.CalibrationMatrix.MaterialEntry

/-! Complete exact matrix-entry generation from the stored cube coordinates. -/
namespace Maxwell.Cost.CalibrationMatrix.StencilEntry
open Structured BankArray WordSchedule
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def code (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq MaterialHeader.code (.seq TestEntry.code (.seq (DirectionSelect.code 90)
    (.seq (.call (Rewind.program 90)) (MaterialEntry.code 90 material z D))))

def costCap (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ) : ℕ :=
  MaterialHeader.costCap width+3500*(width+1)+410+MaterialEntry.costBound material z D

def changes : Finset ℕ := MaterialHeader.changes ∪ WordSchedule.changes TestInputs.plan ∪ {30,31,90}

structure Frame (s t : Store) : Prop where
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ i, 3 ≤ i → i ∉ changes → t.val.tapes i = s.val.tapes i

private theorem emit_key (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (key : StencilKey)
    (input : List Bool) (tape : ℕ → Bool) (origin : ℤ) (s : Store)
    (hkey : s.val.tapes 90 = BitTape.shifted (TableKey.encode key) origin)
    (h30 : Blank s.val 30) (h31 : Blank s.val 31) :
    ∃ cost t, cost ≤ MaterialEntry.costBound material z D ∧
      Executes input tape (MaterialEntry.code 90 material z D) cost s t ∧
      RationalAccumulator.Word t.val 30 (entryChannels material z D key).1 ∧
      RationalAccumulator.Word t.val 31 (entryChannels material z D key).2 ∧
      Blank t.val 90 ∧ BinaryPrecision.Frame {90,30,31} s.val t.val := by
  obtain ⟨t,he,hp,hn,hk,hf⟩ := MaterialTable.executes 90 30 31 (by decide) (by decide)
    (by decide) input tape (TableKey.encode key) (MaterialEntry.table material z D) origin s hkey h30 h31
  have hb := MaterialTable.fixed_cost_bound (TableKey.encode key) (MaterialEntry.table material z D)
  have ht : MaterialEntry.table material z D (TableKey.encode key) = entryChannels material z D key := by
    simp [MaterialEntry.table,TableKey.decode_encode]
  refine ⟨8*34+10*((MaterialEntry.table material z D (TableKey.encode key)).1.size+
      (MaterialEntry.table material z D (TableKey.encode key)).2.size)+14,t,?_,?_,?_,?_,?_,hf⟩
  · simp only [TableKey.encode_length] at hb
    dsimp only [MaterialEntry.costBound]
    omega
  · simpa only [MaterialEntry.code,TableKey.encode_length] using he
  · simpa only [ht] using hp
  · simpa only [ht] using hn
  · exact ⟨origin+(TableKey.encode key).length,hk⟩

/-- Every key bit and emitted integer channel is obtained by executed
arithmetic and Boolean code from the stored operands. -/
theorem executes (material : Cell20 → ℚ) (z : ℚ) (D R width : ℕ)
    (clockWord direction : List Bool) (raw : Fin 7 → List Bool)
    (hwidth : 2 ≤ width) (hclock : clockWord.length = width)
    (hraw : ∀ i, (raw i).length+1 ≤ width) (rd cd : Direction)
    (hrd : addressValue (raw 0) = rd.val) (hcd : addressValue direction = cd.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Banks TestInputs.domain s (TestInputs.initial clockWord raw))
    (hdir : Word s.val 170 direction) (hR : Word s.val 127 (R%20).bits)
    (hclock2 : Word s.val 129 (3 : ℕ).bits) (hclock5 : Word s.val 130 (31 : ℕ).bits)
    (hradix : Word s.val 131 (20 : ℕ).bits)
    (hwork : HeaderCoordinate.WorkBlank s.val) (h135 : Blank s.val 135)
    (hscratch : HeaderCoordinate.ScratchBlank s.val)
    (h90 : Blank s.val 90) (h30 : Blank s.val 30) (h31 : Blank s.val 31) :
    ∃ cost t, cost ≤ costCap material z D width ∧
      Executes input tape (code material z D) cost s t ∧
      RationalAccumulator.Word t.val 30 (entryChannels material z D
        (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).1 ∧
      RationalAccumulator.Word t.val 31 (entryChannels material z D
        (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).2 ∧
      Banks TestInputs.domain t (TestInputs.prepared width clockWord raw) ∧
      HeaderCoordinate.WorkBlank t.val ∧ Blank t.val 135 ∧
      HeaderCoordinate.ScratchBlank t.val ∧ Blank t.val 90 ∧ Frame s t := by
  let coords : Direction → List Bool := fun j => raw (Fin.ofNat 7 (j.val+4))
  have coordWords (j : Direction) : Word s.val (171+j.val) (coords j) := by
    fin_cases j
    · change Word s.val 171 (raw 4)
      simpa [TestInputs.initial] using hb 171 (by decide)
    · change Word s.val 172 (raw 5)
      simpa [TestInputs.initial] using hb 172 (by decide)
    · change Word s.val 173 (raw 6)
      simpa [TestInputs.initial] using hb 173 (by decide)
  have coordLengths (j : Direction) : (coords j).length ≤ width := by
    change (raw (Fin.ofNat 7 (j.val+4))).length ≤ width
    exact (Nat.le_succ _).trans (hraw _)
  obtain ⟨origin,h90⟩ := h90
  obtain ⟨a,m,hca,ea,hmkey,hmwork,hm135,hmscratch,hf⟩ := MaterialHeader.executes input tape R width
    rd cd (TestEntry.rowValues raw) (TestEntry.columnValues raw) direction coords hcd
    (fun _ => rfl) coordLengths origin s hdir coordWords hR hclock2 hclock5 hradix h90 hwork h135 hscratch
  have hmbanks : Banks TestInputs.domain m (TestInputs.initial clockWord raw) := by
    intro i hi
    have hn : ∀ i ∈ TestInputs.domain, i ∉ MaterialHeader.changes := by decide
    exact hf.word (hn i hi) (hb i hi)
  have hms : Scratch m.val := ⟨hmscratch 0 (by decide),hmscratch 1 (by decide),
    hmscratch 2 (by decide),hmscratch 3 (by decide),hmscratch 5 (by decide),
    hmscratch 6 (by decide),hmscratch 8 (by decide),hmscratch 9 (by decide)⟩
  obtain ⟨b,n,hcb,eb,hnd,hnc,hnbanks,hns,hg⟩ := TestEntry.executes width clockWord raw hwidth hclock hraw
    rd hrd input tape m hmbanks hms
  have keepTest (i : ℕ) (hi : 3 ≤ i) (hn : i ∉ WordSchedule.changes TestInputs.plan) :
      n.val.tapes i = m.val.tapes i := hg.tapes i hi hn
  have nkey := (keepTest 90 (by decide) (by decide)).trans hmkey
  have ndir : Word n.val 170 direction := word_of_eq (keepTest 170 (by decide) (by decide))
    (hf.word (by decide) hdir)
  obtain ⟨c,p,hcc,ec,hpkey,hh⟩ := DirectionSelect.executes 90 input tape direction R rd cd
    (TestEntry.rowValues raw) (TestEntry.columnValues raw) origin n ndir hcd hnd hnc nkey
  let key := entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
    (unsignedEdge R cd (TestEntry.columnValues raw))
  obtain ⟨q,eq,hqkey,hj⟩ := HeaderWords.rewind 90 input tape (TableKey.encode key) origin p hpkey
  have qblank (i : ℕ) (hi : i = 30 ∨ i = 31) (hs : Blank s.val i) : Blank q.val i := by
    apply hj.blank (by simp; omega)
    apply hh.blank (by simp; omega)
    apply RationalAccumulator.blank_of_eq (keepTest i (by omega) (by rcases hi with rfl | rfl <;> decide))
    exact hf.blank (by rcases hi with rfl | rfl <;> decide) hs
  obtain ⟨d,t,hcd,ed,hp,hn,h90,hk⟩ := emit_key material z D key input tape origin q hqkey
    (qblank 30 (by simp) h30) (qblank 31 (by simp) h31)
  have tail := HeaderCoordinate.join (HeaderCoordinate.join hh hj) hk
  have tailKeep (i : ℕ) (hi : i ≠ 90 ∧ i ≠ 30 ∧ i ≠ 31) : t.val.tapes i = n.val.tapes i :=
    tail.tapes i (by simpa [and_assoc,and_left_comm,and_comm] using hi)
  have nScratch : HeaderCoordinate.ScratchBlank n.val := by
    intro i hi
    interval_cases i
    · exact hns.1
    · exact hns.2.1
    · exact hns.2.2.1
    · exact hns.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (keepTest 4 (by decide) (by decide)) (hmscratch 4 (by decide))
    · exact hns.2.2.2.2.1
    · exact hns.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (keepTest 7 (by decide) (by decide)) (hmscratch 7 (by decide))
    · exact hns.2.2.2.2.2.2.1
    · exact hns.2.2.2.2.2.2.2
  refine ⟨a+(b+(c+(4*(TableKey.encode key).length+6+d))),t,?_,ea.seq (eb.seq (ec.seq (eq.seq ed))),
    hp,hn,?_,?_,?_,?_,h90,?_⟩
  · rw [TableKey.encode_length]
    dsimp [costCap]
    omega
  · intro i hi
    have hhigh : ∀ i ∈ TestInputs.domain, 100 ≤ i := by decide
    exact word_of_eq (tailKeep i (by have := hhigh i hi; omega)) (hnbanks i hi)
  · intro i hi hi'
    apply RationalAccumulator.blank_of_eq (tailKeep i (by omega))
    apply RationalAccumulator.blank_of_eq (keepTest i (by omega) ?_)
    · exact hmwork i hi hi'
    · have hfinit : ∀ i ∈ Finset.Icc 80 86, i ∉ WordSchedule.changes TestInputs.plan := by decide
      exact hfinit i (by simp; omega)
  · exact RationalAccumulator.blank_of_eq (tailKeep 135 (by decide))
      (RationalAccumulator.blank_of_eq (keepTest 135 (by decide) (by decide)) hm135)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (tailKeep i (by omega)) (nScratch i hi)
  · refine ⟨tail.memory.trans (hg.memory.trans hf.memory),
      tail.inputHead.trans (hg.inputHead.trans hf.inputHead),
      tail.randomCursor.trans (hg.randomCursor.trans hf.randomCursor),
      tail.output.trans (hg.output.trans hf.output),?_⟩
    intro i hi hout
    have hparts : i ∉ MaterialHeader.changes ∧ i ∉ WordSchedule.changes TestInputs.plan ∧
        i ≠ 30 ∧ i ≠ 31 ∧ i ≠ 90 := by simpa [changes,not_or,and_assoc,and_left_comm,and_comm] using hout
    exact (tailKeep i ⟨hparts.2.2.2.2,hparts.2.2.1,hparts.2.2.2.1⟩).trans ((keepTest i hi hparts.2.1).trans (hf.tapes i hparts.1))

end Maxwell.Cost.CalibrationMatrix.StencilEntry
