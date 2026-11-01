import Maxwell.Continuum.FourierTensorCalibrationComponent
import Maxwell.Cost.Structured.LiteralFootprint
import Maxwell.Cost.Structured.WordCleanup.Footprint

/-! The component's finite tape footprint and input-position frame are
independent of large static scalar literals and of all runtime data. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 6500000
set_option maxRecDepth 65536

private theorem below_seq (bound : ℕ) (a b : Code)
    (ha : a.tapesBelow bound=true) (hb : b.tapesBelow bound=true) :
    (Code.seq a b).tapesBelow bound=true := by
  simp only [Code.tapesBelow,ha,hb,Bool.true_and]

private theorem positions_seq (a b : Code)
    (ha : a.protectsInputPositions=true) (hb : b.protectsInputPositions=true) :
    (Code.seq a b).protectsInputPositions=true := by
  simp only [Code.protectsInputPositions,ha,hb,Bool.true_and]

theorem complete_below (j : Fin 3) : (ModeAllocation.completeComponentCode j).tapesBelow 6000=true := by
  fin_cases j <;>
    repeat' first
    | decide
    | exact BinaryPrecision.writeCode_tapesBelow _ _ _ (by decide)
    | exact BinaryPrecision.literalCode_tapesBelow _ _ _ (by decide)
    | apply below_seq

theorem complete_positions (j : Fin 3) :
    (ModeAllocation.completeComponentCode j).protectsInputPositions=true := by
  fin_cases j <;>
    repeat' first
    | decide
    | exact BinaryPrecision.writeCode_positions _ _
    | exact BinaryPrecision.literalCode_positions _ _
    | apply positions_seq

private theorem cleanup_below (ports : List ℕ) (bound : ℕ) (hb : ∀i∈ports,i<bound) :
    (WordCleanup.code ports).tapesBelow bound=true := by
  induction ports with
  | nil => rfl
  | cons i rest ih =>
    change (BitRAM.tapesBelow (TapeOps.clear i) bound && (WordCleanup.code rest).tapesBelow bound)=true
    rw [Bool.and_eq_true]
    exact ⟨by simp [BitRAM.tapesBelow,TapeOps.clear,BitRAMInstruction.tapesBelow,hb i (by simp)],
      ih (fun k hk=>hb k (List.mem_cons_of_mem _ hk))⟩

theorem startup_below : code.tapesBelow 6000=true := by
  have zero : (WordCleanup.code ZeroInitialization.clearPorts).tapesBelow 6000=true :=
    cleanup_below _ _ (by simp only [ZeroInitialization.clearPorts,Finset.mem_sort];decide)
  have last : (WordCleanup.code clearPorts).tapesBelow 6000=true :=
    cleanup_below _ _ (by simp only [clearPorts,Finset.mem_sort];decide)
  change ((CalibrationHandoff.code.tapesBelow 6000 &&
    ((WordCleanup.code ZeroInitialization.clearPorts).tapesBelow 6000 &&
      (NatAssign.code ZeroInitialization.plan).tapesBelow 6000)) &&
    (WordCleanup.code clearPorts).tapesBelow 6000)=true
  simp only [Bool.and_eq_true]
  exact ⟨⟨by decide,zero,by decide⟩,last⟩

theorem component_below (j : Fin 3) : (componentCode j).tapesBelow 6000=true :=
  below_seq _ _ _ startup_below (complete_below j)

theorem component_positions (j : Fin 3) : (componentCode j).protectsInputPositions=true := by
  apply positions_seq
  · change ((CalibrationHandoff.code.protectsInputPositions &&
      ((WordCleanup.code ZeroInitialization.clearPorts).protectsInputPositions &&
        (NatAssign.code ZeroInitialization.plan).protectsInputPositions)) &&
      (WordCleanup.code clearPorts).protectsInputPositions)=true
    simp only [Bool.and_eq_true]
    exact ⟨⟨by decide,WordCleanup.code_inputPositions _,by decide⟩,WordCleanup.code_inputPositions _⟩
  · exact complete_positions j

#print axioms component_below
#print axioms component_positions
end Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
