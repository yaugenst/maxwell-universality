import Maxwell.Continuum.CalibrationCentralPrepare
import Maxwell.Continuum.CalibrationCentralMatrixMachine

/-! Execute the isolated central inverse from stored Schur cells. The
arithmetic circuit, input initialization and copies are all charged. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources
  CentralMatrixMachine.code MatrixInverse.width MatrixInverse.costCoefficient

def inverseCode : Code := .call (CentralMatrixMachine.code.compile.renameTapes relocation)
def computeCode : Code := .seq prepareCode inverseCode
def computeCost (B : ℕ) : ℕ := prepareCost B+MatrixInverse.costCoefficient 24*(B+1)^2+1
def sourceMatrix (v : ℕ→Parts) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j=>(v (500+(MatrixInverse.index 24 (i,j)).val)).value

theorem matrixParts_source (v : ℕ→Parts) :
    MatrixInverse.source 24 (valueBank (matrixParts v))=sourceMatrix v := by
  funext i j
  have small:(MatrixInverse.index 24 (i,j)).val<576 := (MatrixInverse.index 24 (i,j)).isLt
  simp only [MatrixInverse.source,valueBank,matrixParts,ite_eq_left small,sourceMatrix]

theorem compute_executes (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (fresh : ∀i,gap≤ i→Blank s.val i)
    (scratch : NatAssign.Scratch s.val) :
    ∃steps t out,Executes input tape computeCode steps s t ∧ steps≤ computeCost B ∧
      Ready bank out (t.renameTapes relocation) ∧ Good bank out ∧
      WidthBank bank (MatrixInverse.width 24 B) out ∧
      (∀i j,(out (MatrixInverse.output 24 i j)).value=rationalMatrixInverse (sourceMatrix v) i j) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,ea,ca,ra,fa⟩:=prepare_executes v B hB width input tape s cells fresh scratch
  obtain ⟨d,b,out,eb,cb,rb,gb,wb,value,_,fb⟩:=CentralMatrixMachine.executes B hB (matrixParts v)
    (matrixParts_width v B hB width) (matrixParts_good v good) input tape (a.renameTapes relocation) ra
  have execution : Executes input tape inverseCode (d+1) a (b.renameTapes relocation) := by
    simpa only [inverseCode,twice] using eb.renamed_call relocation
  have frame : BinaryPrecision.Frame work a.val (b.renameTapes relocation).val := by
    have hf:=fb.renameTapes relocation
    have eq:=congrArg Subtype.val (twice a)
    exact eq ▸ hf
  refine ⟨c+(d+1),b.renameTapes relocation,out,ea.seq execution,?_,?_,gb,wb,?_,fa.trans frame⟩
  · unfold computeCost
    omega
  · simpa only [twice,bank] using rb
  · simpa only [matrixParts_source] using value

#print axioms compute_executes
end Maxwell.Continuum.Calibration.CentralRelocation
