import Maxwell.Continuum.ProfileCosineExecution
import Maxwell.Continuum.DyadicFloorStoredPowerCost

/-! Exact scratch and metadata joins between the profile DFT and the
stored-power dyadic floor. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem floorClean_cosine_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame cosineWorkspace s.val t.val) : DyadicFloor.Clean t.val := by
  have hd : Disjoint (insert 4 (DyadicFloor.extraIds∪NaturalQuotient.workPorts)) cosineWorkspace := by decide
  refine ⟨blank_of_eq (f.tapes 4 (fun hm => Finset.disjoint_left.mp hd (by simp) hm)) h.1,?_⟩
  intro i hi
  exact blank_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem hi) hm)) (h.2 i hi)

theorem floor_power_outside_cosine : (144:ℕ)∉cosineWorkspace := by decide

private theorem clean_floor_frame (T : Finset ℕ) (s t : Store) (v : ℕ→Parts)
    (ht : ∀i∈T,i<1000) (hz : ∀i∈T,Blank s.val i) (hr : Ready dftRegisters v t)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace dftRegisters) s.val t.val)
    (hd : Disjoint (T\RationalDataflow.ids dftRegisters) (DyadicFloor.StoredPower.workspace dftRegisters)) :
    ∀i∈T,Blank t.val i := by
  intro i hi
  by_cases hm : i∈RationalDataflow.ids dftRegisters
  · have hw := hr.1 i hm
    rw [dataValues_small v (ht i hi)] at hw
    exact (zero_word_iff_blank _ _).mp hw
  · exact blank_of_eq (f.tapes i (fun hf => Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨hi,hm⟩) hf)) (hz i hi)

theorem phaseClean_floor_frame {s t : Store} {v : ℕ→Parts} (h : Phase.Runtime.Clean s.val)
    (hr : Ready dftRegisters v t)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace dftRegisters) s.val t.val) :
    Phase.Runtime.Clean t.val := by
  apply clean_floor_frame ((PhaseMachine.Runtime.ids.erase 652).erase 653) s t v
    (fun i hi => Phase.Runtime.ids_small i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) h hr f
  decide

theorem glueClean_floor_frame {s t : Store} {v : ℕ→Parts} (h : Glue.Clean s.val)
    (hr : Ready dftRegisters v t)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace dftRegisters) s.val t.val) :
    Glue.Clean t.val := by
  apply clean_floor_frame (GlueMachine.Runtime.ids.erase 640) s t v
    (fun i hi => Glue.ids_small i (Finset.mem_of_mem_erase hi)) h hr f
  decide

theorem DFTParameters.floor_frame {D P : ℕ} {s t : Store} (h : DFTParameters D P s)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace dftRegisters) s.val t.val) :
    DFTParameters D P t :=
  ⟨word_of_eq (f.tapes 663 (by decide)) h.precision,word_of_eq (f.tapes 667 (by decide)) h.one,
    word_of_eq (f.tapes 668 (by decide)) h.guard,word_of_eq (f.tapes 669 (by decide)) h.range,
    word_of_eq (f.tapes 652 (by decide)) h.phaseRange,word_of_eq (f.tapes 653 (by decide)) h.phasePrecision,
    word_of_eq (f.tapes 640 (by decide)) h.gluePrecision⟩

#print axioms phaseClean_floor_frame
end Maxwell.Continuum.Profile.Runtime
