import Maxwell.Continuum.CalibrationSymmetricSignData

/-! The half factor is written by the machine before executing the fixed
symmetrized definiteness circuit. Every old workspace word is accounted for. -/
namespace Maxwell.Continuum.Calibration.SymmetricSign
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow ExpressionDefiniteness
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] MatrixInverse.registers PolynomialExpression.determinantNodes
  ExpressionDefiniteness.extent ExpressionDefiniteness.control ExpressionDefiniteness.costConstant

def withHalf (v : ℕ→Parts) : ℕ→Parts := Function.update v 576 (Parts.literal (1/2))
def halfCode : Code := NatAssign.code (literalStage 576 (Parts.literal (1/2)))
def signControl : Control := control expressions 577 578
def code : Code := .seq halfCode signControl.code
def result (v : ℕ→Parts) : ℕ→Parts := signControl.evaluate (withHalf v)
def width (B : ℕ) : ℕ := extent expressions*(B+1)
def cost (B : ℕ) : ℕ := stageCost B+costConstant expressions 577 578*(B+1)^2

theorem half_width : (Parts.literal (1/2)).Width 2 := by
  norm_num [Parts.literal,Parts.Width]
  decide +kernel

theorem source_withHalf (v : ℕ→Parts) : source (withHalf v)=source v := by
  funext i j
  simp only [source,withHalf,Function.update_of_ne (Nat.ne_of_lt (index_lt i j))]

theorem executes (v : ℕ→Parts) (B : ℕ) (hB : 2≤ B)
    (hw : WidthBank bank B v) (hg : Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready bank v s) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost B ∧
      Ready bank (result v) t ∧ Good bank (result v) ∧ WidthBank bank (width B) (result v) ∧
      result v 577=Parts.literal (if negativeTest (symmetricRationalMatrix (source v)) then 1 else 0) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  obtain ⟨c,a,e,charge,ra,frame⟩:=literal_executes bank 576 (small_mem 576 (by decide))
    (Parts.literal (1/2)) v B (half_width.mono hB) hw input tape s ready
  have good : Good bank (withHalf v) := hg.update 576 (Parts.literal_valid _)
  have words : WidthBank bank B (withHalf v) := hw.update 576 (half_width.mono hB)
  obtain ⟨d,t,et,dt,rt,gt,wt,value,changed⟩:=control_executes_in expressions 577 578 size (by decide)
    expressions_fit expressions_below (withHalf v) B words good (expressions_safe _ good) input tape a ra
  have values:=RawDefiniteness.positive_value (evaluate expressions (withHalf v))
    (fun i j=>(expressions_safe (withHalf v) good i j).valid)
  rw [expressions_value _ good (by simp [withHalf,Parts.literal_value]),source_withHalf] at values
  change RawDefiniteness.positive (evaluate expressions (withHalf v))=
    negativeTest (symmetricRationalMatrix (source v)) at values
  rw [values] at value
  exact ⟨c+d,t,e.seq et,Nat.add_le_add charge dt,rt,gt,wt,value,frame.trans changed⟩

#print axioms executes
end Maxwell.Continuum.Calibration.SymmetricSign
