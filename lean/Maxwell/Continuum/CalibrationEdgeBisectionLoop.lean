import Maxwell.Continuum.CalibrationEdgeBisectionStep
import Maxwell.Cost.Structured.NaturalCountdown

/-! The complete finite edge loop reads its iteration count from tape851.
Every branch is the actual generated matrix sign, and the final midpoint is
retained as a concrete signed fraction for subsequent energy arithmetic. -/
namespace Maxwell.Continuum.Calibration.EdgeBisection
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] CentralRelocation.bank count gap relocation
  MatrixInverse.tapeBound MatrixInverse.registers PolynomialExpression.determinantNodes
  SymmetricSign.width SymmetricSign.result BasisForcing.bank SchurRow.nodeCount

def loopCode : Code := NaturalCountdown.code 851 29 stepCode
def finishCode : Code := .seq loopCode EdgeBracketMachine.midpointCode

theorem loop_executes (target heap : ℕ) (d : Data) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (state : Ready target heap 0 d s) :
    ∃cost t next,Executes input tape loopCode cost s t ∧ Ready target heap (2*target) next t ∧
      (∀i,860 ≤ i → i<900 → t.val.tapes i=s.val.tapes i) := by
  let invariant (remaining : ℕ) (u : Store) : Prop :=
    remaining ≤ 2*target ∧ ∃d,Ready target heap (2*target-remaining) d u ∧
      ∀i,860 ≤ i → i<900 → u.val.tapes i=s.val.tapes i
  have stable : ∀n s t,BinaryPrecision.Frame ∅ s.val t.val → invariant n s → invariant n t := by
    intro n s t frame ready
    obtain ⟨bound,d,ready,keep⟩:=ready
    exact ⟨bound,d,ready.transfer frame,fun i lo hi=>(frame.tapes i (by simp)).trans (keep i lo hi)⟩
  have body : ∀n s,invariant (n+1) s → RationalAccumulator.Word s.val 851 (n+1) →
      ∃cost t,Executes input tape stepCode cost s t ∧ invariant n t ∧ RationalAccumulator.Word t.val 851 n := by
    intro n u ready _
    obtain ⟨bound,p,ready,keep⟩:=ready
    obtain ⟨cost,t,next,execution,finished,retained⟩:=step_executes target heap (2*target-(n+1)) p
      (by omega) input tape u ready
    have index : 2*target-(n+1)+1=2*target-n := by omega
    rw [index] at finished
    refine ⟨cost,t,execution,⟨by omega,next,finished,fun i lo hi=>(retained i lo hi).trans (keep i lo hi)⟩,?_⟩
    have word:=finished.controller 851 (by decide)
    simpa only [finished.remaining,show 2*target-(2*target-n)=n by omega] using word
  have initial : invariant (2*target) s := ⟨le_rfl,d,by simpa only [Nat.sub_self] using state,by intros;rfl⟩
  have count : RationalAccumulator.Word s.val 851 (2*target) := by
    simpa only [state.remaining,Nat.sub_zero] using state.controller 851 (by decide)
  obtain ⟨cost,t,execution,finished,_,_⟩:=NaturalCountdown.executes 851 29 stepCode input tape
    invariant stable body (2*target) s initial count
  obtain ⟨_,next,ready,retained⟩:=finished
  exact ⟨cost,t,next,execution,by simpa only [Nat.sub_zero] using ready,retained⟩

theorem finish_executes (target heap : ℕ) (d : Data) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (state : Ready target heap 0 d s) :
    ∃cost t next mid,Executes input tape finishCode cost s t ∧ Ready target heap (2*target) next t ∧
      StoredParts.Stored (positivePort 2302) mid t.val ∧ 0<mid.denominator ∧
      mid.Width next.bracketWidth ∧ mid.value=(calibratedEdge target).center ∧
      (∀i,860 ≤ i → i<900 → t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c0,u,out,e0,ready,retained⟩:=loop_executes target heap d input tape s state
  obtain ⟨c1,t,e1,_,bracket,scratch,width,meaning,cells,value,frame⟩:=
    EdgeBracketMachine.midpoint_executes out.bracket _ ready.represents out.bracketWidth
      ready.bracketPositive ready.bracketWidth input tape u ready.bracket ready.basis.ready.parts.2
  let next : Data := { out with
    bracket := EdgeBracketMachine.midpointResult out.bracket
    bracketWidth := out.bracketWidth+7 }
  refine ⟨c0+c1,t,next,EdgeBracketMachine.parts next.bracket 2302,e0.seq e1,?_,
    cells 2302 (by decide),EdgeScalar.midpoint_positive out.bracket ready.represents.1,?_,?_,?_⟩
  · exact ⟨bracket_basis ready.basis frame scratch,bracket,width,by dsimp [next];omega,meaning,
      bracket_controller ready.controller frame,ready.controllerWidth,ready.precision,ready.remaining,
      ready.radius,ready.bounded,bracket_machin ready.machin frame,
      bracket_central ready.central frame scratch,ready.centralWidth,ready.centralPositive⟩
  · exact EdgeBracketMachine.parts_width _ _ width 2302 (by decide)
  · exact value
  · intro i lo hi
    exact (frame.tapes i (bracket_outside i (by omega) (Or.inl (by omega)))).trans (retained i lo hi)

#print axioms loop_executes
#print axioms finish_executes
end Maxwell.Continuum.Calibration.EdgeBisection
