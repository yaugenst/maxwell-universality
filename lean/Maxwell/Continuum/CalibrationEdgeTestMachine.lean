import Maxwell.Continuum.CalibrationEdgeScalarRestartMachine
import Maxwell.Continuum.CalibrationEdgeScalarMeaning

/-! The actual certified edge decision: produce its scalar inputs, reset
and construct all24 Schur columns, and run the isolated symmetric sign test.
Both first and repeated calls return the concrete banks needed by bisection. -/
namespace Maxwell.Continuum.Calibration.EdgeTest
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount
  CentralRelocation.bank count gap relocation MatrixInverse.tapeBound MatrixInverse.registers
  PolynomialExpression.determinantNodes SymmetricSign.width SymmetricSign.result

def code : Code := .seq EdgeScalarRestart.code BasisMatrixSign.code

theorem executes (heap N B P : ℕ) (mid : Parts) (p : ℕ→Parts)
    (positive : 1≤B) (midGood : 0<mid.denominator) (midWidth : mid.Width B)
    (inside : edgeInitial.lo≤mid.value ∧ mid.value≤edgeInitial.hi)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : BasisColumn.State (N+5) heap P p s)
    (precision : RationalAccumulator.Word s.val 850 N) (machin : EdgeScalar.RelocatedFresh s.val)
    (midpoint : StoredParts.Stored (positivePort 2302) mid s.val)
    (fresh : ∀i,gap≤ i→RationalAccumulator.Blank s.val i) :
    ∃steps t out Q,Executes input tape code steps s t ∧ BasisColumn.State (N+5) heap Q out t ∧
      t.val.registers 31=edgeDecision mid.value N ∧ EdgeScalar.RelocatedFresh t.val ∧
      Ready bank (EdgeSignRelocation.result out) (t.renameTapes relocation) ∧
      Good bank (EdgeSignRelocation.result out) ∧
      WidthBank bank (SymmetricSign.width (max 2 Q)) (EdgeSignRelocation.result out) ∧
      (∀k,850≤k→k<900→t.val.tapes k=s.val.tapes k) ∧
      (∀k,6000≤k→k<count→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,_,state0,machin0,middle0,high0⟩:=EdgeScalarRestart.executes
    (N+5) heap N B P mid p positive midGood midWidth input tape s state precision machin midpoint
  have fresh0 : ∀i,gap≤ i→RationalAccumulator.Blank u.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (high0 i (by unfold gap count at hi;omega)) (fresh i hi)
  obtain ⟨c1,t,out,Q,e1,state1,decision,_,_,central,good,width,high1,middle1⟩:=BasisMatrixSign.executes
    (N+5) heap (EdgeScalarRestart.width N B) (EdgeScalar.result N mid) (by omega)
    (EdgeScalar.result_admissible N mid midGood inside) input tape u state0 fresh0
  refine ⟨c0+c1,t,out,Q,e0.seq e1,state1,?_,?_,central,good,width,?_,?_⟩
  · simpa only [EdgeScalar.matrix_eq N mid midGood,edgeDecision] using decision
  · intro i lo hi
    exact RationalAccumulator.blank_of_eq (middle1 i (by omega) hi) (machin0 i lo hi)
  · intro k lo hi
    exact (middle1 k lo (by omega)).trans (middle0 k (by omega) hi)
  · intro k lo hi
    exact (high1 k lo hi).trans (high0 k lo)

theorem reexecutes (heap N B P W : ℕ) (mid : Parts) (p old : ℕ→Parts)
    (positive : 1≤B) (oldPositive : 1≤W) (midGood : 0<mid.denominator) (midWidth : mid.Width B)
    (inside : edgeInitial.lo≤mid.value ∧ mid.value≤edgeInitial.hi)
    (oldWidth : WidthBank bank W old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : BasisColumn.State (N+5) heap P p s)
    (precision : RationalAccumulator.Word s.val 850 N) (machin : EdgeScalar.RelocatedFresh s.val)
    (midpoint : StoredParts.Stored (positivePort 2302) mid s.val)
    (oldReady : Ready bank old (s.renameTapes relocation)) :
    ∃steps t out Q,Executes input tape code steps s t ∧ BasisColumn.State (N+5) heap Q out t ∧
      t.val.registers 31=edgeDecision mid.value N ∧ EdgeScalar.RelocatedFresh t.val ∧
      Ready bank (EdgeSignRelocation.result out) (t.renameTapes relocation) ∧
      Good bank (EdgeSignRelocation.result out) ∧
      WidthBank bank (SymmetricSign.width (max 2 Q)) (EdgeSignRelocation.result out) ∧
      (∀k,850≤k→k<900→t.val.tapes k=s.val.tapes k) ∧
      (∀k,6000≤k→k<count→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,_,state0,machin0,middle0,high0⟩:=EdgeScalarRestart.executes
    (N+5) heap N B P mid p positive midGood midWidth input tape s state precision machin midpoint
  have ready0:=BasisMatrixSign.central_retained old s u oldReady
    (fun k hk=>high0 k (by unfold gap count at hk;omega)) state0.ready.parts.2
  obtain ⟨c1,t,out,Q,e1,state1,decision,_,_,central,good,width,high1,middle1⟩:=BasisMatrixSign.reexecutes
    (N+5) heap (EdgeScalarRestart.width N B) W (EdgeScalar.result N mid) old (by omega) oldPositive
    (EdgeScalar.result_admissible N mid midGood inside) oldWidth input tape u state0 ready0
  refine ⟨c0+c1,t,out,Q,e0.seq e1,state1,?_,?_,central,good,width,?_,?_⟩
  · simpa only [EdgeScalar.matrix_eq N mid midGood,edgeDecision] using decision
  · intro i lo hi
    exact RationalAccumulator.blank_of_eq (middle1 i (by omega) hi) (machin0 i lo hi)
  · intro k lo hi
    exact (middle1 k lo (by omega)).trans (middle0 k (by omega) hi)
  · intro k lo hi
    exact (high1 k lo hi).trans (high0 k lo)

#print axioms executes
#print axioms reexecutes
end Maxwell.Continuum.Calibration.EdgeTest
