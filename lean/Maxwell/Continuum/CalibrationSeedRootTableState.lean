import Maxwell.Continuum.CalibrationSeedRootRowContents
import Maxwell.Continuum.RationalDataflowArrayHighWordFrame

/-! A concrete stored seed table, with every completed row identified by
the fixed six-producer computation. No execution trace is supplied. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

structure TableState (M D B : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (v : ℕ→Parts) (remaining : ℕ) (s : Store) where
  table : PartArray.Table (2*aliasArraySize (3*M+D))
  remaining_le : remaining≤ArrayDecodeMachine.aliasRowCount (3*M+D)
  numbers : ℕ→ℕ
  natural : NatAssign.Bank rowIds numbers s.val
  naturalWidth : ∀i∈rowIds,(numbers i).bits.length≤B
  size : numbers 750=M
  degree : numbers 751=D
  dimension : numbers 785=aliasArraySize (3*M+D)
  side : numbers 786=aliasSide (3*M+D)
  raw : Ready slots (resetParts v) s
  four : RationalAccumulator.Blank s.val 4
  cache : a.Ready s
  ready : table.OutputReady s
  metadata : table.MetadataWidth (producerWidth B)
  positive : 0<addressValue table.width
  fits : producerWidth B≤addressValue table.width
  separated : table.Separated
  disjoint : a.SeparatedFrom table
  correct : ∀row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)),remaining≤row.val→
    ∀j p,table.get (outputCoordinate M D row j p)=
      entryParts M D a (decodedCoordinates (3*M+D) (3*row.val)) j p v

noncomputable def TableState.count_frame {M D B : ℕ} {a : PartArray.Table (2*(2*D+1)^3)}
    {v : ℕ→Parts} {remaining : ℕ} {s t : Store} (h : TableState M D B a v remaining s)
    (f : CountedShifted.Frame 801 s t) : TableState M D B a v remaining t := by
  have frame : BinaryPrecision.Frame {801} s.val t.val :=
    ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,fun i hi=>f.2.2.2.2.2.1 i (by simpa using hi)⟩
  have arrays := PartArray.arrays_high_word (by decide : 216≤801) h.cache h.ready frame
  exact {
    table := h.table
    remaining_le := h.remaining_le
    numbers := h.numbers
    natural := fun i hi=>RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 i (by
      intro he;subst i;exact (by decide : 801∉rowIds) hi)) (h.natural i hi)
    naturalWidth := h.naturalWidth
    size := h.size
    degree := h.degree
    dimension := h.dimension
    side := h.side
    raw := h.raw.count_frame slots _ 801 (by decide) f
    four := RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 4 (by decide)) h.four
    cache := arrays.1
    ready := arrays.2
    metadata := h.metadata
    positive := h.positive
    fits := h.fits
    separated := h.separated
    disjoint := h.disjoint
    correct := h.correct }

#print axioms TableState.count_frame
end Maxwell.Continuum.Calibration.SeedRoot
