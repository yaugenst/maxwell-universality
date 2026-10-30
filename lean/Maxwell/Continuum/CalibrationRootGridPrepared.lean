import Maxwell.Continuum.CalibrationRootGridStartMachine

/-! Input-size and frame facts for the complete coefficient evaluator.
The grid-cube countdown bound follows from the executed five-instruction setup. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def runtimeWidth (B : ℕ) : ℕ := 32*(B+1)

theorem le_runtimeWidth (B : ℕ) : B≤runtimeWidth B := by unfold runtimeWidth;omega

theorem clockValues_width (n : ℕ→ℕ) (B : ℕ) (hB : 1≤B)
    (hn : ∀i∈clockIds,(n i).bits.length≤B) :
    ∀i∈clockIds,(clockValues n i).bits.length≤runtimeWidth B := by
  have hl : ∀a∈clockSetup,a.literalWidth≤B := by
    simp [clockSetup,NatAssign.Instruction.literalWidth,hB]
  simpa only [clockValues,runtimeWidth,show clockSetup.length=5 by rfl,show 2^5=32 by rfl] using
    Calibration.ArrayDecodeMachine.nat_values_width clockIds clockSetup clockSetup_valid n B hn hl

theorem cube_width (n : ℕ→ℕ) (grid B : ℕ) (hB : 1≤B)
    (hn : ∀i∈clockIds,(n i).bits.length≤B) (hgrid : n 331=grid) :
    (grid^3).bits.length≤runtimeWidth B := by
  have hh := clockValues_width n B hB hn 343 (by decide)
  simpa only [(clockValues_result n).2.2.1,hgrid] using hh

theorem inputFacts (grid B : ℕ) (frequency : Fin 3→ℤ) (n : ℕ→ℕ)
    (hgrid : n 331=grid)
    (hfrequency : ∀i,![n 336,n 337,n 338] i=
      ((-(PeriodicSampling.Product.frequency grid frequency)) i).val)
    (hzero : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hn : ∀i∈ids,(n i).bits.length≤B) :
    InputFacts grid frequency (runtimeWidth B) n := by
  refine ⟨hgrid,hfrequency,hzero,?_,?_⟩
  · intro i hi
    exact (hn i (sourceIds_subset hi)).trans (le_runtimeWidth B)
  · intro i hi
    exact (hn i hi).trans (by unfold naturalWidth runtimeWidth;omega)

theorem normalization_outside_sum (S : Finset ℕ) (i : ℕ) (hi : i=343 ∨ i=344) :
    i∉sumWorkspace S := by
  have hr := FractionWord.outside S i (by omega)
  have hg : i∉GlueMachine.Runtime.ids := by rcases hi with rfl|rfl <;> decide
  have hp : i∉PhaseMachine.Runtime.ids := by rcases hi with rfl|rfl <;> decide
  have hd : i∉decodeWorkspace := by rcases hi with rfl|rfl <;> decide
  have hc : i≠342 := by omega
  simp only [sumWorkspace,Finset.mem_union,Finset.mem_singleton,not_or]
  refine ⟨hc,?_⟩
  simp only [sampleWorkspace,Finset.mem_union,not_or]
  refine ⟨hd,?_⟩
  simp only [RootProduct.workspace,Glue.workspace,Glue.allIds,Phase.Runtime.workspace,
    Phase.Runtime.allIds,RationalDataflow.workspace,Finset.mem_union] at *
  tauto

theorem rational_subset_sum (S : Finset ℕ) : RationalDataflow.workspace S⊆sumWorkspace S :=
  (rational_subset_product S).trans
    (Finset.subset_union_right.trans Finset.subset_union_right)

theorem finishValues_other (grid : ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : i≠10 ∧ i≠11 ∧ i≠12) : finishValues grid v i=v i := by
  simp [finishValues,scaleSum,Control.prepend,Control.evaluate,Instruction.update,hi.1,hi.2.1,hi.2.2]

#print axioms cube_width
#print axioms inputFacts
end Maxwell.Continuum.RationalDataflow.RootGrid
