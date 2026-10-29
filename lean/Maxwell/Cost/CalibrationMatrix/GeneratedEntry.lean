import Maxwell.Cost.CalibrationMatrix.StencilEntry
import Maxwell.Cost.CalibrationMatrix.GeneratedCleanup
import Maxwell.Cost.CalibrationMatrix.Term

/-! Exact stencil-entry generation with reusable operand and arithmetic banks. -/
namespace Maxwell.Cost.CalibrationMatrix.GeneratedEntry
open Structured BankArray WordSchedule
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def code (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq (StencilEntry.code material z D) GeneratedCleanup.code

def costCap (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ) : ℕ :=
  StencilEntry.costCap material z D width+33*(6*width+4)+1

def changes : Finset ℕ := StencilEntry.changes ∪ GeneratedCleanup.banks.toFinset

structure Frame (s t : Store) : Prop where
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ i, 3 ≤ i → i ∉ changes → t.val.tapes i = s.val.tapes i

/-- Generate the signed channel pair, then clear every raw coordinate and
comparison operand. The result is ready for the actual indexed array writer. -/
theorem executes (material : Cell20 → ℚ) (z : ℚ) (D R width : ℕ)
    (clockWord direction : List Bool) (raw : Fin 7 → List Bool)
    (hwidth : 2 ≤ width) (hclock : clockWord.length = width)
    (hraw : ∀ i, (raw i).length+1 ≤ width) (hdirection : direction.length ≤ width)
    (rd cd : Direction) (hrd : addressValue (raw 0) = rd.val) (hcd : addressValue direction = cd.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Banks TestInputs.domain s (TestInputs.initial clockWord raw))
    (hdir : Word s.val 170 direction) (hR : Word s.val 127 (R%20).bits)
    (hclock2 : Word s.val 129 (3 : ℕ).bits) (hclock5 : Word s.val 130 (31 : ℕ).bits)
    (hradix : Word s.val 131 (20 : ℕ).bits)
    (hwork : HeaderCoordinate.WorkBlank s.val) (h135 : Blank s.val 135)
    (hscratch : HeaderCoordinate.ScratchBlank s.val) (h90 : Blank s.val 90)
    (hchannels : ∀ i, 30 ≤ i → i ≤ 36 → Blank s.val i) :
    ∃ cost t, cost ≤ costCap material z D width ∧
      Executes input tape (code material z D) cost s t ∧
      Ready t.val (dotValues
        (entryChannels material z D (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).1
        (entryChannels material z D (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).2) ∧
      (∀ i ∈ GeneratedCleanup.banks, Blank t.val i) ∧
      HeaderCoordinate.WorkBlank t.val ∧ Blank t.val 135 ∧
      HeaderCoordinate.ScratchBlank t.val ∧ Blank t.val 90 ∧ Frame s t := by
  obtain ⟨a,m,hca,ea,hp,hn,hbanks,hmwork,hm135,hmscratch,hm90,hf⟩ :=
    StencilEntry.executes material z D R width clockWord direction raw hwidth hclock hraw
      rd cd hrd hcd input tape s hb hdir hR hclock2 hclock5 hradix hwork h135 hscratch h90
      (hchannels 30 (by decide) (by decide)) (hchannels 31 (by decide) (by decide))
  have hmdir : Word m.val 170 direction := word_of_eq (hf.tapes 170 (by decide) (by decide)) hdir
  obtain ⟨b,t,hcb,eb,htblank,hg⟩ := GeneratedCleanup.executes width clockWord direction raw
    hwidth hraw hdirection input tape m hbanks hmdir
  have keep (i : ℕ) (hi : i < 100) : t.val.tapes i = m.val.tapes i :=
    hg.tapes i (by simp [GeneratedCleanup.banks]; omega)
  have htscratch : HeaderCoordinate.ScratchBlank t.val :=
    fun i hi => RationalAccumulator.blank_of_eq (keep i (by omega)) (hmscratch i hi)
  refine ⟨a+b,t,by dsimp [costCap]; omega,ea.seq eb,?_,htblank,?_,?_,htscratch,?_,?_⟩
  · refine ⟨?_,⟨htscratch 0 (by decide),htscratch 1 (by decide),htscratch 2 (by decide),
      htscratch 3 (by decide),htscratch 5 (by decide),htscratch 6 (by decide),
      htscratch 8 (by decide),htscratch 9 (by decide)⟩,htscratch 7 (by decide)⟩
    intro i hi hi'
    by_cases h30 : i = 30
    · subst i
      simpa [dotValues] using RationalAccumulator.word_of_eq (keep 30 (by decide)) hp
    by_cases h31 : i = 31
    · subst i
      simpa [dotValues] using RationalAccumulator.word_of_eq (keep 31 (by decide)) hn
    have hv : dotValues
        (entryChannels material z D (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).1
        (entryChannels material z D (entryKey (unsignedEdge R rd (TestEntry.rowValues raw))
          (unsignedEdge R cd (TestEntry.columnValues raw)))).2 i = 0 := by
      simp [dotValues,h30,h31]
    rw [hv,RationalAccumulator.zero_word_iff_blank]
    apply RationalAccumulator.blank_of_eq (keep i (by omega))
    apply RationalAccumulator.blank_of_eq (hf.tapes i (by omega) ?_)
    · exact hchannels i hi hi'
    · have hh : ∀ j ∈ Finset.Icc 32 36, j ∉ StencilEntry.changes := by decide
      exact hh i (by simp; omega)
  · intro i hi hi'
    exact RationalAccumulator.blank_of_eq (keep i (by omega)) (hmwork i hi hi')
  · exact hg.blank (by decide) hm135
  · exact RationalAccumulator.blank_of_eq (keep 90 (by decide)) hm90
  · refine ⟨hg.memory.trans hf.memory,hg.inputHead.trans hf.inputHead,
      hg.randomCursor.trans hf.randomCursor,hg.output.trans hf.output,?_⟩
    intro i hi hout
    have hh : i ∉ StencilEntry.changes ∧ i ∉ GeneratedCleanup.banks.toFinset := by
      simpa [changes] using hout
    exact (hg.tapes i hh.2).trans (hf.tapes i hi hh.1)

end Maxwell.Cost.CalibrationMatrix.GeneratedEntry
