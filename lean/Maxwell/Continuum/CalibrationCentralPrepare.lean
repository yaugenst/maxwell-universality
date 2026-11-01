import Maxwell.Continuum.CalibrationCentralCopyMachine

/-! Prepare the central circuit from actual retained Schur entries and fresh
isolated tapes. No initialized inverse bank is supplied by the caller. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources

def prepareCode : Code := .seq initializeCode inputCode
def prepareCost (B : ℕ) : ℕ := Initialize.cost bank+1+inputCost B

theorem count_lower : 10000≤count := by
  unfold count
  exact Nat.le_add_left 10000 _

theorem cells_retained (v : ℕ→Parts) {s t : BitRAMState}
    (cells : Cells inputRegisters v s) (frame : BinaryPrecision.Frame work s t) :
    Cells inputRegisters v t := by
  have keep (i : ℕ) (hi : i∈inputPorts) : t.tapes i=s.tapes i := by
    have bounds:=inputPorts_bounds i hi
    exact retained frame i (by omega)
      (bounds.2.trans_le ((by decide : 4228≤10000).trans count_lower))
  intro j hj
  have owned (k : ℕ) (hk : k∈cellPorts j) : k∈inputPorts := by
    simp only [inputPorts,ports,Finset.mem_biUnion]
    exact ⟨j,hj,hk⟩
  have hp : positivePort j∈inputPorts := owned _ (by simp [cellPorts])
  have hn : negativePort j∈inputPorts := owned _ (by simp [cellPorts])
  have hd : denominatorPort j∈inputPorts := owned _ (by simp [cellPorts])
  exact ⟨RationalAccumulator.word_of_eq (keep _ hp) (cells j hj).1,
    RationalAccumulator.word_of_eq (keep _ hn) (cells j hj).2.1,
    RationalAccumulator.word_of_eq (keep _ hd) (cells j hj).2.2⟩

theorem prepare_executes (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (fresh : ∀i,gap≤ i→Blank s.val i)
    (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape prepareCode steps s t ∧ steps≤ prepareCost B ∧
      Ready bank (matrixParts v) (t.renameTapes relocation) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,ea,ca,ra,fa⟩:=initialize_executes input tape s fresh scratch
  obtain ⟨d,t,et,ct,rt,ft⟩:=input_executes v B hB width input tape a (cells_retained v cells fa) ra
  exact ⟨c+d,t,ea.seq et,Nat.add_le_add ca ct,rt,fa.trans ft⟩

#print axioms prepare_executes
end Maxwell.Continuum.Calibration.CentralRelocation
