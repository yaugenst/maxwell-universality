import Maxwell.Continuum.WellStrengthOnsite
import Maxwell.Continuum.WellOriginalWrite
import Maxwell.Continuum.WellMediatorLoad
import Maxwell.Continuum.SourceStrengthTables
import Maxwell.Continuum.WellAxisGeometry
import Maxwell.Continuum.ContinuumCalibrationEnclosures

/-! The strength machine's retained constants are the actual computed
calibration enclosures. Physical target bounds discharge every reciprocal
side condition; they are not assumptions on the final computation. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
open Maxwell.Cost Maxwell.Composition Maxwell.Logical.Routing
open RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

/-- Exact semantic contract for the five raw outputs retained by calibration.
No normalization of their natural numerator and denominator parts is required. -/
structure CalibratedParts where
  mode : Parts
  scale : Parts
  coupling : Fin 3→Parts
  mode_valid : mode.Valid
  scale_valid : scale.Valid
  coupling_valid : ∀j,(coupling j).Valid
  mode_eq : mode.value=(computedEnclosures p S hm).mode.midpoint
  scale_eq : scale.value=alpha p S hm
  coupling_eq : ∀j,(coupling j).value=couplingValue p S hm (computedEnclosures p S hm).coupling j

variable (data : CalibratedParts p S hm)

def values (k : ℕ) : Parts :=
  if k=1 then data.mode else if k=4 then data.scale else
    if k=5 then data.coupling 0 else if k=6 then data.coupling 1 else
    if k=7 then data.coupling 2 else Parts.literal 0

theorem midpoint : (values p S hm data 1).value=(computedEnclosures p S hm).mode.midpoint := by
  simpa only [values,ite_true] using data.mode_eq

theorem scale : (values p S hm data 4).value=alpha p S hm := by
  simpa only [values,show (4:ℕ)≠1 by decide,ite_false,ite_true] using data.scale_eq

theorem coupling (j : Fin 3) :
    (values p S hm data (5+j.val)).value=couplingValue p S hm (computedEnclosures p S hm).coupling j := by
  fin_cases j <;> simp [values,data.coupling_eq]

theorem scale_nonzero : (values p S hm data 4).value ≠ 0 := by
  rw [scale]
  have positive : (0:ℚ)<alpha p S hm := by exact_mod_cast alpha_pos p S hm
  exact positive.ne'

theorem canonical : WellStrengthReset.canonical (values p S hm data)=values p S hm data := by
  funext k
  rw [WellStrengthReset.canonical,resetList_values]
  by_cases hk : k∈WellStrengthReset.targets
  · rw [ite_eq_left hk]
    simp only [WellStrengthReset.targets,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [values]
  · rw [ite_eq_right hk]

theorem good : Good WellStrength.bank (values p S hm data) := by
  intro k _
  unfold values
  split_ifs
  · exact data.mode_valid
  · exact data.scale_valid
  · exact data.coupling_valid 0
  · exact data.coupling_valid 1
  · exact data.coupling_valid 2
  · exact Parts.literal_valid 0

theorem denominator_pos (hb : S.source ≠ 0) (i : SourceDecoration.Vertex S (precision p S hm)) :
    0<(values p S hm data 1).value+targetDiagonal p S hm (computedEnclosures p S hm).coupling i := by
  rw [midpoint]
  let C := computedEnclosures p S hm
  exact WellStrength.onsite_denominator_pos (length_master p S hm) (energyCalibration p S hm)
    (spacing p S hm) C.mode (targetDiagonal p S hm C.coupling i) C.mode_contains C.mode_width
    (targetDiagonal_bound p S hm (energyCalibration p S hm) hb C.coupling C.coupling_contains C.coupling_width i)

theorem original_target {memory : ℕ→Bool} (source : SourceStrengthTables.Represents S (precision p S hm) memory)
    (i : SourcePositive.Vertex S (precision p S hm)) :
    WellOriginalWrite.target (values p S hm data)
      (addressValue (MemoryWord.readBits memory
        (SourceGraph.Positive.base S (precision p S hm)+(SourceStrengthTables.vertexIndex S (precision p S hm) i).val*4) 4))
      (addressValue (MemoryWord.readBits memory
        (4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3)+
          (SourceStrengthTables.vertexIndex S (precision p S hm) i).val*2) 2))=
      targetDiagonal p S hm (computedEnclosures p S hm).coupling (.inl (.inl i)) := by
  rw [WellOriginalWrite.target,scale,SourceStrengthTables.Represents.read_diagonal S (precision p S hm) source i,
    SourceStrengthTables.Represents.read_degree S (precision p S hm) source i]
  rfl

theorem internal_target (e : SourceRouting.Edge S (precision p S hm))
    (i : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S (precision p S hm)) e).length-1)) :
    WellTarget.target .internal (values p S hm data)=
      targetDiagonal p S hm (computedEnclosures p S hm).coupling (.inl (.inr ⟨e,i⟩)) := by
  rw [WellTarget.target,scale,targetDiagonal,PhysicalDiagonal.diagonal_internal]

theorem internal_denominator :
    (values p S hm data 1).value+WellTarget.target .internal (values p S hm data)≠0 := by
  have targetBound : |(WellTarget.target .internal (values p S hm data):ℝ)|≤
      (1/(2:ℝ)^196)*(length p S hm:ℝ)^2 := by
    rw [WellTarget.target,scale]
    push_cast
    rw [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_pos (alpha_pos p S hm)]
    have ha := (spacing_bounds p S hm).2.2.1
    exact (by linarith only [ha] : (2:ℝ)*(alpha p S hm:ℝ)≤6).trans
      (Parameters.terminal_budget (length_master p S hm))
  rw [midpoint]
  let C := computedEnclosures p S hm
  exact (WellStrength.onsite_denominator_pos (length_master p S hm) (energyCalibration p S hm)
    (spacing p S hm) C.mode _ C.mode_contains C.mode_width targetBound).ne'

theorem selected_coupling (geometry : ℕ→ℕ) :
    WellMediatorLoad.coupling geometry (values p S hm data)=
      couplingValue p S hm (computedEnclosures p S hm).coupling
        (WellAxis.select (geometry 976) (geometry 979) (geometry 977) (geometry 980)) := by
  simp only [WellMediatorLoad.coupling,WellAxis.select]
  split_ifs
  · exact coupling p S hm data 0
  · exact coupling p S hm data 1
  · exact coupling p S hm data 2


theorem mediator_target (step : SourceSteps.Step S (precision p S hm)) (geometry : ℕ→ℕ)
    (hx : ∀j,0 ≤ SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).1 j)
    (hy : ∀j,0 ≤ SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).2 j)
    (x0 : geometry 976=(SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).1 0).toNat)
    (y0 : geometry 979=(SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).2 0).toNat)
    (x1 : geometry 977=(SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).1 1).toNat)
    (y1 : geometry 980=(SourceDecorationEnumeration.shiftedPoint
      (SourceSegmentList.pair S (precision p S hm) step).2 1).toNat) :
    -(WellMediatorLoad.coupling geometry (values p S hm data))^2/(values p S hm data 4).value=
      targetDiagonal p S hm (computedEnclosures p S hm).coupling
        (.inr (SourceEdgeEnumeration.toEdge S (precision p S hm) step)) := by
  rw [selected_coupling,scale,x0,y0,x1,y1,WellAxis.natural_select _ _ hx hy,
    WellAxis.shifted_select,SourceEdgeList.direction_pair]
  rfl

theorem numerator_eq (i : SourceDecoration.Vertex S (precision p S hm)) :
    WellStrength.numerator (FiniteAuxiliary.onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm))
      (values p S hm data 1).value (targetDiagonal p S hm (computedEnclosures p S hm).coupling i)=
      (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling i).numerator := by
  rw [midpoint,WellStrength.onsite_numerator]
  rfl

#print axioms denominator_pos
#print axioms original_target
#print axioms internal_target
#print axioms mediator_target
#print axioms numerator_eq
end Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
