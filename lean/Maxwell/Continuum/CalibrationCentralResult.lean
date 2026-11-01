import Maxwell.Continuum.CalibrationCentralOutputMachine

/-! A complete central inverse invocation returns ordinary stored output
cells and retains its canonical internal bank for subsequent invocations. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap MatrixInverse.width

def resultCode : Code := .seq computeCode outputCode
def resultWork : Finset ℕ := work∪outputPorts

theorem outputParts_member (i : ℕ) (hi : i∈outputRegisters) : i-1124∈bank := by
  have bounds : 1700≤ i ∧ i<2276 := Finset.mem_Ico.mp hi
  simp only [bank,MatrixInverse.registers,Finset.mem_range]
  have hbase : MatrixInverse.base 24=1152 := by decide
  rw [hbase]
  omega

theorem outputParts_good (v : ℕ→Parts) (good : Good bank v) : Good outputRegisters (outputParts v) :=
  fun i hi=>good _ (outputParts_member i hi)

theorem outputParts_width (v : ℕ→Parts) (B : ℕ) (width : WidthBank bank B v) :
    WidthBank outputRegisters B (outputParts v) := fun i hi=>width _ (outputParts_member i hi)

theorem outputParts_value (v : ℕ→Parts) (i j : Fin 24) :
    outputParts v (1700+(MatrixInverse.index 24 (i,j)).val)=v (MatrixInverse.output 24 i j) := by
  unfold outputParts MatrixInverse.output
  congr 1
  omega

theorem output_cells_retained (old : ℕ→Parts) {s t : BitRAMState}
    (cells : Cells outputRegisters old s) (frame : BinaryPrecision.Frame work s t) :
    Cells outputRegisters old t := by
  apply cells.transfer_tapes
  intro i hi
  rw [←outputPorts_eq] at hi
  have bounds:=Finset.mem_Ico.mp hi
  exact retained frame i (by omega)
    (bounds.2.trans_le ((by decide : 7828≤10000).trans count_lower))

theorem output_changes_result : {0,1,2,3}∪outputPorts⊆resultWork := by
  intro i hi
  rcases Finset.mem_union.mp hi with scratch|target
  · have low : i<4 := by simp only [Finset.mem_insert,Finset.mem_singleton] at scratch;omega
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_union_left _ scratch,scratch_fixed i low⟩)
  · exact Finset.mem_union_right _ target

theorem finish_executes (v old : ℕ→Parts) (B O c : ℕ) (s a : Store)
    (input : List Bool) (tape : ℕ→Bool)
    (execution : Executes input tape computeCode c s a)
    (ready : Ready bank v (a.renameTapes relocation))
    (good : Good bank v) (width : WidthBank bank B v)
    (cells : Cells outputRegisters old s.val) (oldWidth : WidthBank outputRegisters O old)
    (frame : BinaryPrecision.Frame work s.val a.val) :
    ∃steps t,Executes input tape resultCode steps s t ∧ steps≤c+outputCost (max B O) ∧
      Cells outputRegisters (outputParts v) t.val ∧
      Good outputRegisters (outputParts v) ∧ WidthBank outputRegisters B (outputParts v) ∧
      Ready bank v (t.renameTapes relocation) ∧ BinaryPrecision.Frame resultWork s.val t.val := by
  have w : WidthBank bank (max B O) v := fun i hi=>(width i hi).mono (le_max_left _ _)
  have ow : WidthBank outputRegisters (max B O) old := fun i hi=>(oldWidth i hi).mono (le_max_right _ _)
  obtain ⟨d,t,e,charge,out,retainedBank,changed⟩:=output_executes v old (max B O) w ow input tape a
    ready (output_cells_retained old cells frame)
  exact ⟨c+d,t,execution.seq e,Nat.add_le_add_left charge c,out,outputParts_good v good,
    outputParts_width v B width,retainedBank,
    (frame.mono Finset.subset_union_left).trans (changed.mono output_changes_result)⟩

#print axioms finish_executes
end Maxwell.Continuum.Calibration.CentralRelocation
