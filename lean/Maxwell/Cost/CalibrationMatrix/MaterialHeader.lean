import Maxwell.Cost.CalibrationMatrix.HeaderCoordinate
import Maxwell.Cost.CalibrationMatrix.BooleanKey

namespace Maxwell.Cost.CalibrationMatrix.MaterialHeader
open Structured BankArray HeaderCoordinate
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxHeartbeats 1200000

/-- Direction words may contain high zero padding; the first two bits are
still exactly the canonical two-bit direction field. -/
theorem direction_field (raw : List Bool) (d : Direction) (h : addressValue raw = d.val) :
    FixedWidth.bits 2 raw = TableKey.field 2 d.val := by
  cases raw with
  | nil => fin_cases d <;> simp_all [addressValue, FixedWidth.bits, TableKey.field]
  | cons a tail =>
    cases tail with
    | nil => cases a <;> fin_cases d <;> simp_all [addressValue, FixedWidth.bits, TableKey.field]
    | cons b tail =>
      cases a <;> cases b <;> fin_cases d <;>
        simp_all [addressValue, FixedWidth.bits, TableKey.field] <;> first | decide | omega

def header (R : ℕ) (d : Direction) (column : Direction → ℕ) : List Bool :=
  TableKey.field 2 d.val ++
    (TableKey.field 5 (Phase.phase (column 0 % 20) (R % 20)) ++
    (TableKey.field 5 (Phase.phase (column 1 % 20) (R % 20)) ++
      TableKey.field 5 (Phase.phase (column 2 % 20) (R % 20))))

theorem header_binding (R : ℕ) (rd cd : Direction) (row column : Direction → ℕ) :
    header R cd column = BooleanKey.materialHeader
      (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column)) := by
  simp [header, BooleanKey.materialHeader, entryKey, unsignedEdge, Phase.phase_value,
    edgeMod20, siteMod20, Int.cast_sub]

def changes : Finset ℕ := HeaderCoordinate.changes ∪ {135}

def code : Code := .seq (padWordCode 170 129 135)
  (.seq (.call (TapeOps.copyClear 135 90))
    (.seq (HeaderCoordinate.code 171)
      (.seq (HeaderCoordinate.code 172) (HeaderCoordinate.code 173))))

def costCap (B : ℕ) : ℕ := 2100*(B+8)^2+3200

/-- The complete physical 17-bit material header is emitted from the raw
column digits and stored cube-origin residue, using actual machine code. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (R B : ℕ)
    (rd cd : Direction) (row column : Direction → ℕ)
    (direction : List Bool) (raw : Direction → List Bool)
    (hdirection : addressValue direction = cd.val)
    (hvalues : ∀ j, addressValue (raw j) = column j)
    (hlengths : ∀ j, (raw j).length ≤ B)
    (origin : ℤ) (s : Store)
    (hdir : Word s.val 170 direction)
    (hraw : ∀ j, Word s.val (171+j.val) (raw j))
    (hR : Word s.val 127 (R % 20).bits)
    (hclock2 : Word s.val 129 (3 : ℕ).bits)
    (hclock5 : Word s.val 130 (31 : ℕ).bits)
    (hradix : Word s.val 131 (20 : ℕ).bits)
    (hout : s.val.tapes 90 = {BitTape.blank with head := origin})
    (hwork : WorkBlank s.val) (h135 : Blank s.val 135) (hscratch : ScratchBlank s.val) :
    ∃ cost t, cost ≤ costCap B ∧ Executes input tape code cost s t ∧
      t.val.tapes 90 = BitTape.shiftedEnd (BooleanKey.materialHeader
        (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin ∧
      WorkBlank t.val ∧ Blank t.val 135 ∧ ScratchBlank t.val ∧
      BinaryPrecision.Frame changes s.val t.val := by
  obtain ⟨c1, s1, hc1, e1, w1, f1⟩ := HeaderWords.pad_raw 170 129 135
    (by decide) (by decide) (by decide) input tape 2 (3 : ℕ).bits direction (by decide)
    s hdir hclock2 h135
  rw [direction_field direction cd hdirection] at w1
  obtain ⟨s2, e2, z2, out2, f2⟩ := HeaderWords.append 135 90 (by decide) input tape
    (TableKey.field 2 cd.val) [] origin s1 w1 (by
      rw [f1.tapes 90 (by simp), hout]
      simp [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank])
  have f02 := join f1 f2
  have work2 : WorkBlank s2.val := fun i hi hi' => f02.blank (by simp; omega) (hwork i hi hi')
  have scratch2 : ScratchBlank s2.val := fun i hi => f02.blank (by simp; omega) (hscratch i hi)
  have hr : R % 20 < 20 := Nat.mod_lt R (by decide)
  obtain ⟨c3, s3, hc3, e3, out3, work3, scratch3, f3⟩ := HeaderCoordinate.executes 171 (by decide)
    input tape (raw 0) (TableKey.field 2 cd.val) (R % 20) hr origin s2
    (f02.word (by simp) (hraw 0))
    (f02.word (by simp) hR) (f02.word (by simp) hclock5) (f02.word (by simp) hradix)
    (by simpa using out2) work2 scratch2
  have f03 := join f02 f3
  obtain ⟨c4, s4, hc4, e4, out4, work4, scratch4, f4⟩ := HeaderCoordinate.executes 172 (by decide)
    input tape (raw 1)
    (TableKey.field 2 cd.val ++ TableKey.field 5 (Phase.phase (addressValue (raw 0) % 20) (R % 20)))
    (R % 20) hr origin s3 (f03.word (by simp [HeaderCoordinate.changes]) (hraw 1))
    (f03.word (by simp [HeaderCoordinate.changes]) hR)
    (f03.word (by simp [HeaderCoordinate.changes]) hclock5)
    (f03.word (by simp [HeaderCoordinate.changes]) hradix) out3 work3 scratch3
  have f04 := join f03 f4
  obtain ⟨c5, t, hc5, e5, out5, work5, scratch5, f5⟩ := HeaderCoordinate.executes 173 (by decide)
    input tape (raw 2)
    ((TableKey.field 2 cd.val ++ TableKey.field 5 (Phase.phase (addressValue (raw 0) % 20) (R % 20))) ++
      TableKey.field 5 (Phase.phase (addressValue (raw 1) % 20) (R % 20)))
    (R % 20) hr origin s4 (f04.word (by simp [HeaderCoordinate.changes]) (hraw 2))
    (f04.word (by simp [HeaderCoordinate.changes]) hR)
    (f04.word (by simp [HeaderCoordinate.changes]) hclock5)
    (f04.word (by simp [HeaderCoordinate.changes]) hradix) out4 work4 scratch4
  have he := e1.seq (e2.seq (e3.seq (e4.seq e5)))
  simp only [TableKey.field_length] at he
  refine ⟨_, t, ?_, he, ?_, work5, ?_, scratch5, (join f04 f5).mono ?_⟩
  · have h3 : c3 ≤ 700*(B+8)^2+1000 := hc3.trans (by gcongr; exact hlengths 0)
    have h4 : c4 ≤ 700*(B+8)^2+1000 := hc4.trans (by gcongr; exact hlengths 1)
    have h5 : c5 ≤ 700*(B+8)^2+1000 := hc5.trans (by gcongr; exact hlengths 2)
    dsimp [costCap]
    omega
  · rw [← header_binding R rd cd row column]
    simpa only [header, hvalues, List.append_assoc] using out5
  · exact ((f3.trans f4).trans f5).blank (by simp [HeaderCoordinate.changes]) z2
  · intro i hi
    simpa [changes, HeaderCoordinate.changes, or_assoc, or_left_comm, or_comm] using hi

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (R B : ℕ)
    (rd cd : Direction) (row column : Direction → ℕ)
    (direction : List Bool) (raw : Direction → List Bool)
    (hdirection : addressValue direction = cd.val)
    (hvalues : ∀ j, addressValue (raw j) = column j)
    (hlengths : ∀ j, (raw j).length ≤ B)
    (origin : ℤ) (s : Store)
    (hdir : Word s.val 170 direction)
    (hraw : ∀ j, Word s.val (171+j.val) (raw j))
    (hR : Word s.val 127 (R % 20).bits)
    (hclock2 : Word s.val 129 (3 : ℕ).bits)
    (hclock5 : Word s.val 130 (31 : ℕ).bits)
    (hradix : Word s.val 131 (20 : ℕ).bits)
    (hout : s.val.tapes 90 = {BitTape.blank with head := origin})
    (hwork : WorkBlank s.val) (h135 : Blank s.val 135) (hscratch : ScratchBlank s.val) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap B+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap B+1) s.val).instructions ≤ costCap B ∧
      t.val.tapes 90 = BitTape.shiftedEnd (BooleanKey.materialHeader
        (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin ∧
      WorkBlank t.val ∧ Blank t.val 135 ∧ ScratchBlank t.val ∧
      BinaryPrecision.Frame changes s.val t.val := by
  obtain ⟨cost, t, hc, he, ht⟩ := executes input tape R B rd cd row column direction raw hdirection
    hvalues hlengths origin s hdir hraw hR hclock2 hclock5 hradix hout hwork h135 hscratch
  have hr := he.compiled_run (costCap B+1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ht⟩

end Maxwell.Cost.CalibrationMatrix.MaterialHeader
