import Maxwell.Continuum.CalibrationCentralResult

/-! End-to-end central inversion: stored Schur inputs become ordinary inverse
cells through executed initialization, arithmetic, and output copies. The
same program supports its first and all subsequent calls. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap MatrixInverse.width

theorem executes (v previousOutput : ℕ→Parts) (B O : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (oldWidth : WidthBank outputRegisters O previousOutput)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (oldCells : Cells outputRegisters previousOutput s.val)
    (fresh : ∀i,gap≤ i→Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃steps t out,Executes input tape resultCode steps s t ∧
      steps≤computeCost B+outputCost (max (MatrixInverse.width 24 B) O) ∧
      Cells outputRegisters (outputParts out) t.val ∧
      Ready bank out (t.renameTapes relocation) ∧ Good bank out ∧
      WidthBank bank (MatrixInverse.width 24 B) out ∧
      (∀i j,(outputParts out (1700+(MatrixInverse.index 24 (i,j)).val)).value=
        rationalMatrixInverse (sourceMatrix v) i j) ∧
      BinaryPrecision.Frame resultWork s.val t.val := by
  obtain ⟨c,a,out,e,charge,ready,g,w,value,frame⟩:=compute_executes v B hB width good input tape s cells fresh scratch
  obtain ⟨d,t,et,dt,stored,_,_,retainedBank,changed⟩:=finish_executes _ previousOutput
    (MatrixInverse.width 24 B) O c s a input tape e ready g w oldCells oldWidth frame
  exact ⟨d,t,_,et,dt.trans (Nat.add_le_add_right charge _),stored,retainedBank,g,w,
    fun i j=>by rw [outputParts_value];exact value i j,changed⟩

theorem reexecutes (v old previousOutput : ℕ→Parts) (B W O : ℕ) (hB : 1≤ B) (hW : 1≤ W)
    (width : WidthBank inputRegisters B v) (good : Good inputRegisters v)
    (internalWidth : WidthBank bank W old) (oldWidth : WidthBank outputRegisters O previousOutput)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (oldCells : Cells outputRegisters previousOutput s.val)
    (initialBank : Ready bank old (s.renameTapes relocation)) :
    ∃steps t out,Executes input tape resultCode steps s t ∧
      steps≤reuseCost B W+outputCost (max (MatrixInverse.width 24 B) O) ∧
      Cells outputRegisters (outputParts out) t.val ∧
      Ready bank out (t.renameTapes relocation) ∧ Good bank out ∧
      WidthBank bank (MatrixInverse.width 24 B) out ∧
      (∀i j,(outputParts out (1700+(MatrixInverse.index 24 (i,j)).val)).value=
        rationalMatrixInverse (sourceMatrix v) i j) ∧
      BinaryPrecision.Frame resultWork s.val t.val := by
  obtain ⟨c,a,out,e,charge,ready,g,w,value,frame⟩:=reuse_executes v old B W hB hW width good internalWidth
    input tape s cells initialBank
  obtain ⟨d,t,et,dt,stored,_,_,retainedBank,changed⟩:=finish_executes _ previousOutput
    (MatrixInverse.width 24 B) O c s a input tape e ready g w oldCells oldWidth frame
  exact ⟨d,t,_,et,dt.trans (Nat.add_le_add_right charge _),stored,retainedBank,g,w,
    fun i j=>by rw [outputParts_value];exact value i j,changed⟩

#print axioms executes
#print axioms reexecutes
end Maxwell.Continuum.Calibration.CentralRelocation
