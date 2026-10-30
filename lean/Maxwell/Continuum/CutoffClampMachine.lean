import Maxwell.Continuum.CutoffRawEvaluation
import Maxwell.Continuum.RationalDataflowControlResults

/-! Exact runtime clipping to the cutoff integration interval. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def clampControl : Control :=
  .step (.literal 1 (1/2))
    (.step (.binary .sub 2 0 1)
      (.positive 2 (.step (.literal 0 (1/2)) .done)
        (.step (.literal 1 (-1/2))
          (.step (.binary .sub 2 1 0)
            (.positive 2 (.step (.literal 0 (-1/2)) .done) .done)))))

theorem clampControl_steps : clampControl.steps=7 := rfl

theorem clampControl_valid (S : Finset ℕ) (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) :
    clampControl.Valid S := by
  simp only [clampControl,Control.Valid,Instruction.Valid,h0,h1,h2,and_self]

theorem clampControl_literals (W : ℕ) (hW : 2≤W) : clampControl.LiteralsFit W := by
  have hp : (Parts.literal (1/2:ℚ)).Width W := (Parts.literal_width cutoff_half_width).mono hW
  have hm : (Parts.literal (-1/2:ℚ)).Width W :=
    (Parts.literal_width (by simpa only [neg_div] using cutoff_half_width.neg)).mono hW
  simp only [clampControl,Control.LiteralsFit,Instruction.LiteralFits,hp,hm,and_self]

theorem clampControl_admissible (v : ℕ→Parts) : clampControl.AdmissibleTrace v := by
  simp only [clampControl,Control.AdmissibleTrace,Instruction.Admissible,
    ite_self,and_self]

private theorem step_apply (op : Instruction) (rest : Control) (v : ℕ→Parts) (i : ℕ) :
    (.step op rest : Control).evaluate v i=rest.evaluate (op.update v) i := rfl

private theorem done_apply (v : ℕ→Parts) (i : ℕ) : (.done : Control).evaluate v i=v i := rfl

private theorem positive_apply (source : ℕ) (yes no : Control) (v : ℕ→Parts) (i : ℕ) :
    (.positive source yes no : Control).evaluate v i=
      if 0<(v source).value then yes.evaluate v i else no.evaluate v i := by
  by_cases hp : 0<(v source).value
  · simp only [Control.evaluate,hp,ite_true]
  · simp only [Control.evaluate,hp,ite_false]

theorem clampControl_value (v : ℕ→Parts) (hv : (v 0).Valid) :
    clampControl.evaluate v 0=clamp (v 0) := by
  have hp : ((v 0).sub (Parts.literal (1/2))).value=(v 0).value-1/2 := by
    rw [Parts.sub_value _ _ hv (Parts.literal_valid _),Parts.literal_value]
  have hm : ((Parts.literal (-1/2)).sub (v 0)).value= -1/2-(v 0).value := by
    rw [Parts.sub_value _ _ (Parts.literal_valid _) hv,Parts.literal_value]
  have hp' : (0<((v 0).sub (Parts.literal (1/2))).value) ↔ (1/2:ℚ)<(v 0).value := by
    rw [hp]
    exact sub_pos
  have hm' : (0<((Parts.literal (-1/2)).sub (v 0)).value) ↔ (v 0).value<(-1/2:ℚ) := by
    rw [hm]
    exact sub_pos
  simp only [clampControl,step_apply,done_apply,positive_apply,Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (0:ℕ)≠1),
    Function.update_of_ne (by decide : (0:ℕ)≠2),clamp]
  simp only [hp',hm']

theorem clampControl_keep (v : ℕ→Parts) (i : ℕ) (h0 : i≠0) (h1 : i≠1) (h2 : i≠2) :
    clampControl.evaluate v i=v i := by
  simp only [clampControl,step_apply,done_apply,positive_apply,Instruction.update,
    Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2,ite_self]

theorem clamp_executes (S : Finset ℕ) (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S)
    (v : ℕ→Parts) (W : ℕ) (hW : 2≤W) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t output, Executes input tape clampControl.code cost s t ∧
      cost≤7*operationCost (128*(W+1))+1 ∧ Ready S output t ∧ Good S output ∧
      WidthBank S (128*(W+1)) output ∧ output 0=clamp (v 0) ∧
      (∀ i, i≠0 → i≠1 → i≠2 → output i=v i) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have valid := clampControl_valid S h0 h1 h2
  have width := clampControl.automatic_widthTrace S valid v W hw (clampControl_literals W hW)
  have width' : clampControl.WidthTrace S (128*(W+1)) v := by
    simpa only [clampControl_steps,show (2:ℕ)^7=128 by norm_num] using width
  obtain ⟨cost,t,he,hcost,hready,hframe⟩ := clampControl.executes S valid v _ width'
    hg (clampControl_admissible v) input tape s hs
  refine ⟨cost,t,clampControl.evaluate v,he,?_,hready,
    clampControl.evaluate_good S valid v hg (clampControl_admissible v),width'.result,
    clampControl_value v (hg 0 h0),clampControl_keep v,hframe⟩
  simpa only [clampControl_steps] using hcost

#print axioms clamp_executes
end Maxwell.Continuum.Calibration.RawCutoff
