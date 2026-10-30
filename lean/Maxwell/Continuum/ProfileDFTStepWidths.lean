import Maxwell.Continuum.ProfileDFTStepData

/-! Additive raw-word growth of the profile transform's cached accumulator. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 2500000

theorem dftStepValues_width (S : Finset ℕ) (D P U B W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hx : (v 0).Width (U+1)) (hk : (v 5).Width (U+1))
    (hacc : (v 9).Width B) (hD : D≤U) (hP : P≤U)
    (hscratch : dftScratchWidth U≤W) (hB : B+dftTermWidth U+1≤W) :
    WidthBank S W (dftStepValues D P v) := by
  have hw0 := angularValues_width S P U W v hw hx hP (by unfold dftScratchWidth at hscratch;omega)
  have hw1 : WidthBank S W (dftAfterPreparation P v) :=
    (dftPreparation_width S P U W v hw0 hx hk (by unfold dftScratchWidth at hscratch;omega)).2.2
  have hw2 := dftAfterPhase_width S D P U W v hw1 hx hk hD hP
    (by unfold dftScratchWidth at hscratch;omega)
  exact (dftFinish_width S D P U B W v hw2 hx hk hacc hD hP hB).2.2.2.2

#print axioms dftStepValues_width
end Maxwell.Continuum.Profile.Runtime
