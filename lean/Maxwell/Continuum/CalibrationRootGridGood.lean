import Maxwell.Continuum.CalibrationRootGridAccumulate

/-! Every raw denominator in the literal grid sample remains positive.
This follows from the arithmetic recipe and requires no machine trace. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost
set_option maxHeartbeats 2500000

theorem RootSample.values_good (S : Finset ℕ) (hS : RootSample.inputs⊆S)
    (N : ℕ) (v : ℕ→Parts) (hg : Good S v) : Good S (RootSample.values N v) := by
  have ha := RootSample.argument.evaluate_good S (RootSample.argument_valid S hS) v hg
    (RootSample.argument_admissible v)
  have hc (i : Fin 3) : (RootSample.coordinates v i).Valid := by
    apply hg
    apply hS
    have hi := i.isLt
    simp only [RootSample.inputs,Finset.mem_insert,Finset.mem_singleton]
    omega
  exact ha.update 4 (Glue.result_valid N _ (RootSample.rawArgument_valid _ hc))

theorem RootProduct.values_good (S : Finset ℕ) (hS : RootProduct.inputs⊆S)
    (N : ℕ) (v : ℕ→Parts) (hg : Good S v) : Good S (RootProduct.values N v) := by
  have hr := RootSample.values_good S (RootProduct.root_inputs.trans hS) N v hg
  have hphase := hg 5 (hS (by decide))
  have hc : Good S (RootProduct.afterCos N v) := hr.update 6
    (Phase.result_valid RationalTaylor.cosineSigns 1 N (v 5) hphase)
  have hs : Good S (RootProduct.afterSin N v) := hc.update 7
    (Phase.result_valid RationalTaylor.sineSigns 1 N (v 5) hphase)
  exact RootProduct.multiply.evaluate_good S (RootProduct.multiply_valid S hS) _ hs
    (RootProduct.multiply_admissible _)

theorem RootGridCenter.values_good (S : Finset ℕ) (hS : RootGridCenter.inputs⊆S)
    (v : ℕ→Parts) (hg : Good S v) : Good S (RootGridCenter.values v) := by
  have h0 : Good S (RootGridCenter.first v) := (RootGridCenter.center 0).evaluate_good S
    (RootGridCenter.center_valid S hS 0) v hg (RootGridCenter.center_admissible 0 v)
  have h1 : Good S (RootGridCenter.second v) := (RootGridCenter.center 1).evaluate_good S
    (RootGridCenter.center_valid S hS 1) _ h0 (RootGridCenter.center_admissible 1 _)
  have h2 : Good S (RootGridCenter.centered v) := (RootGridCenter.center 2).evaluate_good S
    (RootGridCenter.center_valid S hS 2) _ h1 (RootGridCenter.center_admissible 2 _)
  exact RootGridCenter.scale.evaluate_good S (RootGridCenter.scale_valid S hS) _ h2
    (RootGridCenter.scale_admissible _)

theorem RootGrid.sampleParts_good (S : Finset ℕ) (hS : RootGridCenter.inputs⊆S)
    (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (hg : Good S v) (hpos : 0<n 331) :
    Good S (RootGrid.sampleParts N n v) := by
  have hn : 0<RootGrid.values n 331 := by rw [RootGrid.values_keep n 331 (by decide)];exact hpos
  have hl := RootGrid.loadParts_good S (RootGrid.values n) v hg hn
  have hc := RootGridCenter.values_good S hS _ hl
  exact RootProduct.values_good S ((show RootProduct.inputs⊆RootGridCenter.inputs by decide).trans hS) N _ hc

#print axioms RootGrid.sampleParts_good
end Maxwell.Continuum.RationalDataflow
