import Maxwell.Continuum.CalibrationEdgeBisectionState

/-! One actual edge iteration: integer midpoint, generated Schur sign,
integer bracket update, and the canonical runtime countdown decrement. -/
namespace Maxwell.Continuum.Calibration.EdgeBisection
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] CentralRelocation.bank count gap relocation
  MatrixInverse.tapeBound MatrixInverse.registers PolynomialExpression.determinantNodes
  SymmetricSign.width SymmetricSign.result BasisForcing.bank SchurRow.nodeCount

def stepCode : Code := .seq EdgeBracketMachine.midpointCode
  (.seq EdgeTest.code (.seq EdgeBracketMachine.stepCode EdgeController.advanceCode))

theorem step_executes (target heap k : ℕ) (d : Data) (more : k<2*target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (state : Ready target heap k d s) :
    ∃cost t next,Executes input tape stepCode cost s t ∧ Ready target heap (k+1) next t ∧
      (∀i,860 ≤ i → i<900 → t.val.tapes i=s.val.tapes i) := by
  let I:=edgeBrackets edgeDecision 182 edgeInitial k
  let vm:=EdgeBracketMachine.midpointResult d.bracket
  let mid:=EdgeBracketMachine.parts vm 2302
  obtain ⟨c0,s0,e0,_,bracket0,scratch0,width0,meaning0,cells0,value0,frame0⟩:=
    EdgeBracketMachine.midpoint_executes d.bracket I state.represents d.bracketWidth
      state.bracketPositive state.bracketWidth input tape s state.bracket state.basis.ready.parts.2
  have basis0 : BasisColumn.State ((188+k)+5) heap d.scalarWidth d.scalar s0 := by
    convert bracket_basis state.basis frame0 scratch0 using 1;omega
  have control0:=bracket_controller state.controller frame0
  have precision0 : RationalAccumulator.Word s0.val 850 (188+k) := by
    simpa only [state.precision] using control0 850 (by decide)
  have midGood : 0<mid.denominator := EdgeScalar.midpoint_positive d.bracket state.represents.1
  have midWidth : mid.Width (d.bracketWidth+7) :=
    EdgeBracketMachine.parts_width vm _ width0 2302 (by decide)
  have inside : edgeInitial.lo ≤ mid.value ∧ mid.value ≤ edgeInitial.hi := by
    rw [show mid.value=I.midpoint from value0]
    exact EdgeScalar.bracket_midpoint_inside k
  obtain ⟨c1,s1,out,Q,e1,basis1,decision,machin1,central1,_,centralWidth1,interval1,high1⟩:=
    EdgeTest.reexecutes heap (188+k) (d.bracketWidth+7) d.scalarWidth d.centralWidth mid
      d.scalar d.central (by omega) state.centralPositive midGood midWidth inside state.centralWidth
      input tape s0 basis0 precision0 (bracket_machin state.machin frame0)
      (cells0 2302 (by decide)) (bracket_central state.central frame0 scratch0)
  have bracket1 : NatAssign.Bank (SignedBracket.ids EdgeBracketMachine.base) vm s1.val := by
    intro i hi
    have bounds:=bracket_bounds i hi
    exact RationalAccumulator.word_of_eq (high1 i (by omega) (by unfold count;omega)) (bracket0 i hi)
  have control1 : NatAssign.Bank EdgeController.activeIds d.control s1.val := by
    intro i hi
    rcases controller_bounds i hi with rfl | bounds
    · rw [state.radius]
      have word:=basis1.ready.naturals 311
        (Finset.mem_union_left _ (BasisForcing.naturalIds_decode (by decide)))
      simpa only [BasisReentry.radius,show 188+k+5=193+k by omega] using word
    · exact RationalAccumulator.word_of_eq (interval1 i bounds.1 (by omega)) (control0 i hi)
  obtain ⟨c2,s2,e2,_,bracket2,scratch2,width2,meaning2,_,frame2⟩:=
    EdgeBracketMachine.step_executes vm I meaning0 (d.bracketWidth+7) (by omega) width0
      (edgeDecision mid.value (188+k)) input tape s1 bracket1 basis1.ready.parts.2 decision
  have control2:=bracket_controller control1 frame2
  obtain ⟨c3,t,e3,_,control3,scratch3,width3,_,_,radius3,frame3⟩:=
    EdgeController.advance_executes d.control d.controlWidth (by rw [state.remaining];omega)
      state.controllerWidth input tape s2 control2 scratch2
  let next : Data :=
    { scalar:=out
      bracket:=EdgeBracketMachine.stepResult (edgeDecision mid.value (188+k)) vm
      control:=EdgeController.advancedValues d.control
      central:=EdgeSignRelocation.result out
      scalarWidth:=Q
      bracketWidth:=d.bracketWidth+14
      controlWidth:=EdgeController.advanceWidth d.controlWidth
      centralWidth:=max 1 (SymmetricSign.width (max 2 Q)) }
  have finished : Ready target heap (k+1) next t := by
    have fields:=EdgeController.advanced_fields d.control
    refine ⟨?_,controller_bracket bracket2 frame3,?_,by dsimp [next];omega,?_,
      control3,width3,?_,?_,?_,by omega,
      controller_machin (bracket_machin machin1 frame2) frame3,
      controller_central (bracket_central central1 frame2 scratch2) frame3 scratch3,?_,le_max_left _ _⟩
    · apply (bracket_basis basis1 frame2 scratch2).rebase frame3 scratch3
      simpa only [state.precision,show 188+k+6=193+(k+1) by omega] using radius3
    · simpa only [next,show d.bracketWidth+7+7=d.bracketWidth+14 by omega] using width2
    · rw [edgeBrackets]
      simpa only [next,show mid.value=I.midpoint from value0,show 182+k+6=188+k by omega] using meaning2
    · change EdgeController.advancedValues d.control 850=188+(k+1)
      rw [fields.1,state.precision]
      omega
    · change EdgeController.advancedValues d.control 851=2*target-(k+1)
      rw [fields.2.1,state.remaining]
      omega
    · change EdgeController.advancedValues d.control 311=193+(k+1)
      rw [fields.2.2.1,state.precision]
      omega
    · exact fun i hi=>(centralWidth1 i hi).mono (le_max_right _ _)
  refine ⟨c0+(c1+(c2+c3)),t,next,e0.seq (e1.seq (e2.seq e3)),finished,?_⟩
  intro i lo hi
  exact (frame3.tapes i (controller_outside i (by omega) (by omega) (Or.inr lo))).trans
    ((frame2.tapes i (bracket_outside i (by omega) (Or.inl (by omega)))).trans
      ((interval1 i (by omega) hi).trans
        (frame0.tapes i (bracket_outside i (by omega) (Or.inl (by omega))))))

#print axioms step_executes
end Maxwell.Continuum.Calibration.EdgeBisection
