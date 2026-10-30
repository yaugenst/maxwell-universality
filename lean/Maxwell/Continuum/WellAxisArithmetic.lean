import Maxwell.Continuum.WellAxisGeometry
import Maxwell.Continuum.WellTargetExecution

/-! The actual mediator coupling is selected by two equality tests on
stored coordinates. Squared differences implement equality using the
already checked rational positivity branch. -/
namespace Maxwell.Continuum.RationalDataflow.WellAxisMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000

def copyCoupling (source : ℕ) : Control :=
  .step (.literal 13 0) (.step (.binary .add 8 source 13) .done)

def control : Control :=
  .step (.binary .sub 12 8 9) (.step (.binary .mul 12 12 12)
    (.positive 12 (copyCoupling 5)
      (.step (.binary .sub 12 10 11) (.step (.binary .mul 12 12 12)
        (.positive 12 (copyCoupling 6) (copyCoupling 7))))))

def selected (v : ℕ→Parts) : ℚ :=
  if (v 8).value≠(v 9).value then (v 5).value else
    if (v 10).value≠(v 11).value then (v 6).value else (v 7).value

theorem valid : control.Valid WellStrength.bank := by
  simp [control,copyCoupling,Control.Valid,Instruction.Valid,WellStrength.bank]

theorem admissible (v : ℕ→Parts) : control.AdmissibleTrace v := by
  simp [control,copyCoupling,Control.AdmissibleTrace,Instruction.Admissible]

theorem fits : control.LiteralsFit 1 := by
  have h0 : (Parts.literal 0).Width 1 := by norm_num [Parts.literal,Parts.Width]
  simp only [control,copyCoupling,Control.LiteralsFit,Instruction.LiteralFits]
  exact ⟨trivial,trivial,⟨h0,trivial,trivial⟩,trivial,trivial,
    ⟨h0,trivial,trivial⟩,h0,trivial,trivial⟩

theorem output_value (v : ℕ→Parts) (hg : Good WellStrength.bank v) :
    (control.evaluate v 8).value=selected v := by
  have he := congrFun (control.evaluate_value WellStrength.bank valid v hg (admissible v)) 8
  simpa [control,copyCoupling,Control.rationalEvaluate,Instruction.rationalUpdate,valueBank,
    selected,mul_self_pos,sub_ne_zero] using he

theorem preserves (v : ℕ→Parts) (i : ℕ) (h8 : i≠8) (h12 : i≠12) (h13 : i≠13) :
    control.evaluate v i=v i := by
  simp only [control,copyCoupling,Control.evaluate]
  split_ifs <;> simp [Instruction.update,h8,h12,h13]

theorem executes (v : ℕ→Parts) (W : ℕ) (hW : 1≤W) (hw : WidthBank WellStrength.bank W v)
    (hg : Good WellStrength.bank v) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (hs : Ready WellStrength.bank v s) :
    ∃cost t,Executes input tape control.code cost s t ∧ cost≤2^126*(W+2)^2 ∧
      Ready WellStrength.bank (control.evaluate v) t ∧ Good WellStrength.bank (control.evaluate v) ∧
      WidthBank WellStrength.bank (256*(W+1)) (control.evaluate v) ∧
      (control.evaluate v 8).value=selected v ∧
      BinaryPrecision.Frame (workspace WellStrength.bank) s.val t.val := by
  have tr := control.automatic_widthTrace WellStrength.bank valid v W hw (fits.mono hW)
  have tr' : control.WidthTrace WellStrength.bank (256*(W+1)) v := tr
  obtain ⟨cost,t,ex,hc,hr,hf⟩ := control.executes WellStrength.bank valid v _ tr' hg (admissible v) input tape s hs
  refine ⟨cost,t,ex,?_,hr,control.evaluate_good _ valid v hg (admissible v),tr'.result,output_value v hg,hf⟩
  change cost≤8*operationCost (256*(W+1))+1 at hc
  unfold operationCost at hc
  nlinarith only [hc,Nat.zero_le W]

#print axioms output_value
#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellAxisMachine
