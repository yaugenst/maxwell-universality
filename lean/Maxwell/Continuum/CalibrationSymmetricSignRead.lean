import Maxwell.Continuum.CalibrationSymmetricSignMachine
import Maxwell.Continuum.CalibrationCentralReset
import Maxwell.Continuum.RationalDataflowBankTransfer
import Maxwell.Cost.Structured.BooleanWord

/-! Run the sign circuit in the central workspace and read its actual Boolean
word into branch register31. Stored data and scratch remain reusable. -/
namespace Maxwell.Continuum.Calibration.EdgeSignRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap SymmetricSign.width
  SymmetricSign.code SymmetricSign.cost SymmetricSign.result

def signCode : Code := .call (SymmetricSign.code.compile.renameTapes relocation)
def readCode : Code := BooleanWord.code (relocation (positivePort 577)) 31 30
def testedCode : Code := .seq signCode readCode
def test (v : ℕ→Parts) : Bool := negativeTest (symmetricRationalMatrix (SymmetricSign.source v))

theorem read_executes (v : ℕ→Parts) (value : Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready bank v (s.renameTapes relocation))
    (result : v 577=Parts.literal (if value then 1 else 0)) :
    ∃t,Executes input tape readCode 3 s t ∧ t.val.registers 31=value ∧
      Ready bank v (t.renameTapes relocation) ∧ BinaryPrecision.Frame ∅ s.val t.val := by
  have member : 577∈bank := SymmetricSign.bank_eq ▸ SymmetricSign.small_mem 577 (by decide)
  have stored:=ready.1 (positivePort 577) (cell_mem member (by simp [cellPorts]))
  rw [dataValues_positive,result] at stored
  have natural : RationalAccumulator.Word (s.renameTapes relocation).val (positivePort 577)
      (if value then 1 else 0) := by
    cases value <;> simpa [Parts.literal] using stored
  obtain ⟨origin,word⟩:=natural
  have actual : RationalAccumulator.Word s.val (relocation (positivePort 577)) (if value then 1 else 0) :=
    ⟨origin,(state_tape s _).symm.trans word⟩
  obtain ⟨t,execution,bool,frame⟩:=BooleanWord.executes (relocation (positivePort 577)) 31 30 (by decide)
    value input tape s actual
  refine ⟨t,execution,bool,ready.transfer_tapes ?_,frame⟩
  intro i _
  rw [state_tape,state_tape]
  exact frame.tapes _ (by simp)

theorem tested_executes (v : ℕ→Parts) (B : ℕ) (hB : 2≤ B)
    (width : WidthBank bank B v) (good : Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready bank v (s.renameTapes relocation)) :
    ∃steps t,Executes input tape testedCode steps s t ∧ steps≤SymmetricSign.cost B+4 ∧
      t.val.registers 31=test v ∧ Ready bank (SymmetricSign.result v) (t.renameTapes relocation) ∧
      Good bank (SymmetricSign.result v) ∧ WidthBank bank (SymmetricSign.width B) (SymmetricSign.result v) ∧
      BinaryPrecision.Frame work s.val t.val := by
  have w : WidthBank SymmetricSign.bank B v := by simpa only [SymmetricSign.bank_eq] using width
  have g : Good SymmetricSign.bank v := by simpa only [SymmetricSign.bank_eq] using good
  have r : Ready SymmetricSign.bank v (s.renameTapes relocation) := by
    simpa only [SymmetricSign.bank_eq] using ready
  obtain ⟨c,a,e,charge,ra,ga,wa,value,changed⟩:=SymmetricSign.executes v B hB w g
    input tape (s.renameTapes relocation) r
  have execution : Executes input tape signCode (c+1) s (a.renameTapes relocation) := by
    simpa only [signCode,twice] using e.renamed_call relocation
  have resulting : Ready bank (SymmetricSign.result v) ((a.renameTapes relocation).renameTapes relocation) := by
    simpa only [twice,SymmetricSign.bank_eq] using ra
  have frame : BinaryPrecision.Frame work s.val (a.renameTapes relocation).val := by
    have hf:=changed.renameTapes relocation
    rw [SymmetricSign.bank_eq] at hf
    have eq:=congrArg Subtype.val (twice s)
    exact eq ▸ hf
  obtain ⟨t,et,bool,rt,ft⟩:=read_executes (SymmetricSign.result v) (test v) input tape
    (a.renameTapes relocation) resulting value
  refine ⟨c+1+3,t,execution.seq et,by omega,bool,rt,?_,?_,frame.trans (ft.mono (by simp))⟩
  · simpa only [SymmetricSign.bank_eq] using ga
  · simpa only [SymmetricSign.bank_eq] using wa

#print axioms tested_executes
end Maxwell.Continuum.Calibration.EdgeSignRelocation
