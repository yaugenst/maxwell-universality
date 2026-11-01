import Maxwell.Continuum.CalibrationSymmetricSignRead

/-! The bisection test consumes actual Schur cells, initializes or reuses the
central workspace, and returns the executed symmetrized sign in register31. -/
namespace Maxwell.Continuum.Calibration.EdgeSignRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
open RationalAccumulator (Blank)
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap SymmetricSign.width
  SymmetricSign.code SymmetricSign.cost SymmetricSign.result

def matrix (v : ℕ→Parts) : Matrix (Fin 24) (Fin 24) ℚ := fun i j=>(v (500+24*i.val+j.val)).value
def code : Code := .seq prepareCode testedCode
def cost (B : ℕ) : ℕ := prepareCost B+SymmetricSign.cost B+4
def reuseCost (B W : ℕ) : ℕ := Initialize.resetCost bank W+1+inputCost B+SymmetricSign.cost B+4
def result (v : ℕ→Parts) : ℕ→Parts := SymmetricSign.result (matrixParts v)

theorem source_value (v : ℕ→Parts) : SymmetricSign.source (matrixParts v)=matrix v := by
  funext i j
  change (matrixParts v (SymmetricSign.index i j)).value=(v (500+24*i.val+j.val)).value
  rw [matrixParts,ite_eq_left (SymmetricSign.index_lt i j)]
  simp only [SymmetricSign.index,Nat.add_assoc]

theorem executes (v : ℕ→Parts) (B : ℕ) (hB : 2≤ B)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (fresh : ∀i,gap≤ i→Blank s.val i)
    (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost B ∧
      t.val.registers 31=negativeTest (symmetricRationalMatrix (matrix v)) ∧
      Ready bank (result v) (t.renameTapes relocation) ∧ Good bank (result v) ∧
      WidthBank bank (SymmetricSign.width B) (result v) ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,e,charge,ready,frame⟩:=prepare_executes v B (by omega) width input tape s cells fresh scratch
  obtain ⟨d,t,et,dt,bool,rt,gt,wt,ft⟩:=tested_executes (matrixParts v) B hB
    (matrixParts_width v B (by omega) width) (matrixParts_good v good) input tape a ready
  refine ⟨c+d,t,e.seq et,?_,?_,rt,gt,wt,frame.trans ft⟩
  · unfold cost
    omega
  · simpa only [test,source_value] using bool

theorem reexecutes (v old : ℕ→Parts) (B W : ℕ) (hB : 2≤ B) (hW : 1≤ W)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (oldWidth : WidthBank bank W old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (ready : Ready bank old (s.renameTapes relocation)) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤reuseCost B W ∧
      t.val.registers 31=negativeTest (symmetricRationalMatrix (matrix v)) ∧
      Ready bank (result v) (t.renameTapes relocation) ∧ Good bank (result v) ∧
      WidthBank bank (SymmetricSign.width B) (result v) ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,e,charge,ra,fa⟩:=reset_executes old W hW oldWidth input tape s ready
  obtain ⟨d,b,eb,cb,rb,fb⟩:=input_executes v B (by omega) width input tape a (cells_retained v cells fa) ra
  obtain ⟨f,t,et,ct,bool,rt,gt,wt,ft⟩:=tested_executes (matrixParts v) B hB
    (matrixParts_width v B (by omega) width) (matrixParts_good v good) input tape b rb
  refine ⟨c+d+f,t,(e.seq eb).seq et,?_,?_,rt,gt,wt,(fa.trans fb).trans ft⟩
  · unfold reuseCost
    omega
  · simpa only [test,source_value] using bool

#print axioms executes
#print axioms reexecutes
end Maxwell.Continuum.Calibration.EdgeSignRelocation
