import Maxwell.Continuum.CalibrationNeumannLoop
import Maxwell.Continuum.CalibrationNeumannWidths

/-! Uniform bit-machine semantics of the shared-denominator Neumann iteration. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
open RationalAccumulator (Blank)
set_option maxHeartbeats 2000000

theorem uniform_compiled_run {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D : ℕ)
    (hD : 0<D) (b : Channels n) (hdecode : a.Decodes A D (b,b))
    (aBound bBound N B : ℕ) (hA : A.Bounded aBound) (hb : b.Bounded bBound)
    (hW : uniformWidth n aBound bBound D N≤addressValue a.data.width)
    (hsized : a.data.Sized B) (hm : n*n<2^B) (hn : n<2^B)
    (input : List Bool) (tape : ℕ→Bool) (count outer : List Bool)
    (hcount : addressValue count=n) (hcl : count.length≤B)
    (houter : addressValue outer=N) (hol : outer.length≤B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140=BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).finished=some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).instructions≤
        3600000*(N+1)*(n+1)^2*(B+2)^2 ∧
      (a.iterate N).Ready count B t.val ∧ Blank t.val 140 ∧ Horner.Outside a.data s.val t.val ∧
      (∀ i : Fin n, ((Horner.channels (a.iterate N).words 10 11).value i : ℚ)/(D:ℚ)^(N+1)=
        sharedRationalIteration D A.value b.value (N+1) i) := by
  have hfit := Snapshot.iterate_fits hdecode hA hb N hW
  obtain ⟨t,hrun,hcost,hready,hblank,houtside⟩ := compiled_run a N B hsized hm hn hfit input tape
    count outer hcount hcl houter hol origin s hs h140
  have hdec := Snapshot.iterate_decodes hdecode N hfit
  refine ⟨t,hrun,hcost.trans (costCap_le N n B),hready,hblank,houtside,?_⟩
  intro i
  rw [hdec.value]
  exact channels_rational_value A D hD b N i

#print axioms uniform_compiled_run

end Maxwell.Continuum.Calibration.NeumannMachine
