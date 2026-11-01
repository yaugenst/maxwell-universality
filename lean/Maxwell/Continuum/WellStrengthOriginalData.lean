import Maxwell.Continuum.WellStrengthChronological

/-! The original pass reads the exact diagonal and degree arrays retained
by source routing, reindexed only by the proved original-vertex count. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
open Maxwell.Cost Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow SourceDecorationEnumeration
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable (data : CalibratedParts p S hm)

def diagonalWords : Vector (List Bool)
    ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length) := Vector.ofFn fun i=>
  (PositiveGraph.Invariant.sourceDiagonalWords S (precision p S hm)).get
    (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i)

def degreeWords : Vector (List Bool)
    ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length) := Vector.ofFn fun i=>
  (IncidenceEncoding.words 2 (IncidenceRanks.run (SourceGraph.Incidence.endpoint S (precision p S hm))
    (4*SourceGraph.Positive.count S (precision p S hm)) le_rfl).counters).get
    (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i)

theorem diagonal_represented {memory : ℕ→Bool}
    (h : SourceStrengthTables.Represents S (precision p S hm) memory) :
    BitArray.Represents memory (SourceGraph.Positive.base S (precision p S hm)) 4 (diagonalWords p S hm) := by
  refine { length := ?_, bits := ?_ }
  case refine_1 =>
    intro i
    simpa only [diagonalWords,Calibration.vector_get_ofFn] using h.diagonal.length (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i)
  case refine_2 =>
    intro i j hj
    simpa only [diagonalWords,Calibration.vector_get_ofFn,Fin.cast] using h.diagonal.bits (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i) j hj

theorem degree_represented {memory : ℕ→Bool}
    (h : SourceStrengthTables.Represents S (precision p S hm) memory) :
    BitArray.Represents memory
      (4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3))
      2 (degreeWords p S hm) := by
  refine { length := ?_, bits := ?_ }
  case refine_1 =>
    intro i
    simpa only [degreeWords,Calibration.vector_get_ofFn] using h.counter.length (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i)
  case refine_2 =>
    intro i j hj
    simpa only [degreeWords,Calibration.vector_get_ofFn,Fin.cast] using h.counter.bits (Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i) j hj

theorem original_word_target
    (i : Fin ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length)) :
    WellOriginalWrite.target (values p S hm data) (addressValue ((diagonalWords p S hm).get i))
      (addressValue ((degreeWords p S hm).get i))=
      targetDiagonal p S hm (computedEnclosures p S hm).coupling
        (.inl (.inl ((SourceEnumeration.vertexEquiv S (precision p S hm)).symm i))) := by
  let vertex := (SourceEnumeration.vertexEquiv S (precision p S hm)).symm i
  have index : SourceStrengthTables.vertexIndex S (precision p S hm) vertex=
      Fin.cast (SourceGraph.Incidence.vertex_count S (precision p S hm)) i := by
    simp only [SourceStrengthTables.vertexIndex,vertex,Equiv.apply_symm_apply]
  rw [WellOriginalWrite.target,scale]
  simp only [diagonalWords,degreeWords,Calibration.vector_get_ofFn]
  erw [←index,SourceStrengthTables.diagonal_value,SourceStrengthTables.degree_value]
  rfl

theorem original_part {saved} (h : Represents S (precision p S hm) saved)
    (i : Fin ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length)) :
    Parts.literal (WellStrength.numerator (wellStoredPrecision p S hm) (values p S hm data 1).value
      (WellOriginalWrite.target (values p S hm data) (addressValue ((diagonalWords p S hm).get i))
        (addressValue ((degreeWords p S hm).get i))):ℚ)=
      Parts.literal (wellNumerators p S hm i.val:ℚ) := by
  rw [original_word_target,wellNumerators_at p S hm _ _ (Represents.original_vertex_lookup S (precision p S hm) h i)]
  rw [show wellStoredPrecision p S hm=FiniteAuxiliary.onsitePrecision (length p S hm)
    (spacing p S hm) (length_pos p S hm) from rfl,numerator_eq]

theorem original_denominator (hb : S.source≠0)
    (i : Fin ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length)) :
    (values p S hm data 1).value+
      WellOriginalWrite.target (values p S hm data) (addressValue ((diagonalWords p S hm).get i))
        (addressValue ((degreeWords p S hm).get i))≠0 := by
  rw [original_word_target]
  exact (denominator_pos p S hm data hb _).ne'

#print axioms original_word_target
#print axioms original_part
#print axioms original_denominator
end Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
