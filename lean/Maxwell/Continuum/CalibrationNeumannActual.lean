import Maxwell.Continuum.CalibrationNeumannCost
import Maxwell.Continuum.CalibrationArrayAffine

/-! The uniform integer machine computes the literal cached calibration array.
This leaf specifies its already stored input table; table construction and
loading are separate stages. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Cost.CalibrationMatrix.Horner
open RationalAccumulator (Blank)
set_option maxHeartbeats 2000000

theorem cached_sharedRationalIteration (t E : ℚ) (r : Fin 3→ℚ) (R : ℕ)
    (f : RationalRealField) (K : ℕ) (i : Fin (aliasArraySize R)) :
    sharedRationalIteration (cachedDenominator t E r R f)
      (cachedIntegerTransition t E r R f) (cachedIntegerSource t E r R f) K i =
        (cachedInverseApply t E r R f K).get i := by
  rw [← sharedNumerator_sound _ (cachedDenominator_pos t E r R f)]
  exact cachedInteger_iteration t E r R f K i

theorem cached_compiled_run (t E : ℚ) (r : Fin 3→ℚ) (R : ℕ) (f : RationalRealField)
    (a : Snapshot (aliasArraySize R))
    (hdecode : a.Decodes (integerMatrix (cachedIntegerTransition t E r R f))
      (cachedDenominator t E r R f)
      (integerChannels (cachedIntegerSource t E r R f),
       integerChannels (cachedIntegerSource t E r R f)))
    (aBound bBound N B : ℕ)
    (hA : (integerMatrix (cachedIntegerTransition t E r R f)).Bounded aBound)
    (hb : (integerChannels (cachedIntegerSource t E r R f)).Bounded bBound)
    (hW : uniformWidth (aliasArraySize R) aBound bBound (cachedDenominator t E r R f) N≤
      addressValue a.data.width)
    (hsized : a.data.Sized B) (hm : aliasArraySize R*aliasArraySize R<2^B)
    (hn : aliasArraySize R<2^B)
    (input : List Bool) (tape : ℕ→Bool) (count outer : List Bool)
    (hcount : addressValue count=aliasArraySize R) (hcl : count.length≤B)
    (houter : addressValue outer=N) (hol : outer.length≤B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140=BitTape.shifted outer origin) :
    ∃ out : Store,
      (runPriced (code.compile.next input tape)
        (costCap N (aliasArraySize R) B+1) s.val).finished=some (out.place code.size) ∧
      (runPriced (code.compile.next input tape)
        (costCap N (aliasArraySize R) B+1) s.val).instructions≤
          3600000*(N+1)*(aliasArraySize R+1)^2*(B+2)^2 ∧
      (a.iterate N).Ready count B out.val ∧ Blank out.val 140 ∧
      Horner.Outside a.data s.val out.val ∧
      (∀ i : Fin (aliasArraySize R),
        ((Horner.channels (a.iterate N).words 10 11).value i : ℚ)/
          (cachedDenominator t E r R f : ℚ)^(N+1)=
            (cachedInverseApply t E r R f (N+1)).get i) := by
  obtain ⟨out,hrun,hcost,hready,hblank,houtside,hvalue⟩ := uniform_compiled_run a
    (integerMatrix (cachedIntegerTransition t E r R f)) (cachedDenominator t E r R f)
    (cachedDenominator_pos t E r R f) (integerChannels (cachedIntegerSource t E r R f))
    hdecode aBound bBound N B hA hb hW hsized hm hn input tape count outer hcount hcl
    houter hol origin s hs h140
  refine ⟨out,hrun,hcost,hready,hblank,houtside,fun i => ?_⟩
  rw [hvalue,integerMatrix_value,integerChannels_value]
  exact cached_sharedRationalIteration t E r R f (N+1) i

#print axioms cached_compiled_run
end Maxwell.Continuum.Calibration.NeumannMachine
