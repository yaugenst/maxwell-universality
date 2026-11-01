import Maxwell.Continuum.CalibrationCentralExecute

/-! Reusing the central workspace clears each old word as part of its
charged literal assignment. A previous inverse therefore supplies the next
initialization state without assuming fresh tapes on repeated calls. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources
  CentralMatrixMachine.code MatrixInverse.width MatrixInverse.costCoefficient

def reuseCost (B W : ℕ) : ℕ :=
  Initialize.resetCost bank W+1+inputCost B+MatrixInverse.costCoefficient 24*(B+1)^2+1

theorem reset_executes (old : ℕ→Parts) (W : ℕ) (hW : 1≤ W)
    (width : WidthBank bank W old) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready bank old (s.renameTapes relocation)) :
    ∃steps t,Executes input tape initializeCode steps s t ∧ steps≤Initialize.resetCost bank W+1 ∧
      Ready bank Initialize.parts (t.renameTapes relocation) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,a,execution,charge,ra,frame⟩:=Initialize.reset_executes bank old W hW width
    input tape (s.renameTapes relocation) ready
  refine ⟨steps+1,a.renameTapes relocation,?_,Nat.add_le_add_right charge 1,?_,?_⟩
  · simpa only [initializeCode,twice] using execution.renamed_call relocation
  · simpa only [twice] using ra
  · have hf:=frame.renameTapes relocation
    have eq:=congrArg Subtype.val (twice s)
    exact eq ▸ hf

theorem reuse_executes (v old : ℕ→Parts) (B W : ℕ) (hB : 1≤ B) (hW : 1≤ W)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (oldWidth : WidthBank bank W old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (ready : Ready bank old (s.renameTapes relocation)) :
    ∃steps t out,Executes input tape computeCode steps s t ∧ steps≤ reuseCost B W ∧
      Ready bank out (t.renameTapes relocation) ∧ Good bank out ∧
      WidthBank bank (MatrixInverse.width 24 B) out ∧
      (∀i j,(out (MatrixInverse.output 24 i j)).value=rationalMatrixInverse (sourceMatrix v) i j) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,ea,ca,ra,fa⟩:=reset_executes old W hW oldWidth input tape s ready
  obtain ⟨d,b,eb,cb,rb,fb⟩:=input_executes v B hB width input tape a (cells_retained v cells fa) ra
  obtain ⟨e,u,out,eu,cu,ru,gu,wu,value,_,fu⟩:=CentralMatrixMachine.executes B hB (matrixParts v)
    (matrixParts_width v B hB width) (matrixParts_good v good) input tape (b.renameTapes relocation) rb
  have execution : Executes input tape inverseCode (e+1) b (u.renameTapes relocation) := by
    simpa only [inverseCode,twice] using eu.renamed_call relocation
  have frame : BinaryPrecision.Frame work b.val (u.renameTapes relocation).val := by
    have hf:=fu.renameTapes relocation
    have eq:=congrArg Subtype.val (twice b)
    exact eq ▸ hf
  refine ⟨(c+d)+(e+1),u.renameTapes relocation,out,(ea.seq eb).seq execution,?_,?_,gu,wu,?_,(fa.trans fb).trans frame⟩
  · unfold reuseCost
    omega
  · simpa only [twice,bank] using ru
  · simpa only [matrixParts_source] using value

#print axioms reuse_executes
end Maxwell.Continuum.Calibration.CentralRelocation
