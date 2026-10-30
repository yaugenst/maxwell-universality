import Maxwell.Continuum.RationalExpressionLayout

/-! Exact raw-word semantics for the finite expression compiler. -/

namespace Maxwell.Continuum.Calibration.RationalExpression

open RationalDataflow

theorem instructions_result (e : RationalExpression) (s : ℕ) (he : e.Below s) (v : ℕ → Parts) :
    RationalDataflow.evaluate (e.instructions s) v (e.output s)=e.evaluate v := by
  induction e generalizing s v with
  | input i => rfl
  | zero => exact Function.update_self _ _ _
  | binary op a b ia ib =>
    let va := RationalDataflow.evaluate (a.instructions s) v
    let vb := RationalDataflow.evaluate (b.instructions (s+a.slots)) va
    have ha := ia s he.1 v
    have hb := ib (s+a.slots) (he.2.mono (by omega)) va
    change va (a.output s)=a.evaluate v at ha
    change vb (b.output (s+a.slots))=b.evaluate va at hb
    have hkeep : vb (a.output s)=va (a.output s) :=
      instructions_frame b (s+a.slots) va (a.output s) (Or.inl (output_lt a s he.1))
    have hbe : b.evaluate va=b.evaluate v := b.evaluate_congr s he.2 va v
      (fun i hi => instructions_frame a s v i (Or.inl hi))
    simp only [instructions,output,RationalDataflow.evaluate_append,RationalDataflow.evaluate,
      Instruction.update,Function.update_self]
    change op.eval (vb (a.output s)) (vb (b.output (s+a.slots)))=op.eval (a.evaluate v) (b.evaluate v)
    rw [hkeep,ha,hb,hbe]
  | inverse a ih =>
    have ha := ih s he v
    simp only [instructions,output,RationalDataflow.evaluate_append,RationalDataflow.evaluate,
      Instruction.update,Function.update_self]
    change (RationalDataflow.evaluate (a.instructions s) v (a.output s)).inverse=(a.evaluate v).inverse
    rw [ha]

theorem admissibleTrace_append (xs ys : List Instruction) (v : ℕ → Parts) :
    RationalDataflow.AdmissibleTrace (xs++ys) v ↔
      RationalDataflow.AdmissibleTrace xs v ∧
        RationalDataflow.AdmissibleTrace ys (RationalDataflow.evaluate xs v) := by
  induction xs generalizing v with
  | nil => simp only [List.nil_append,RationalDataflow.AdmissibleTrace,RationalDataflow.evaluate,true_and]
  | cons a xs ih =>
    simp only [List.cons_append,RationalDataflow.AdmissibleTrace,RationalDataflow.evaluate,ih]
    tauto

theorem instructions_admissible (e : RationalExpression) (s : ℕ) (he : e.Below s)
    (v : ℕ → Parts) (hs : e.Safe v) : RationalDataflow.AdmissibleTrace (e.instructions s) v := by
  induction e generalizing s v with
  | input i => trivial
  | zero => exact ⟨trivial,trivial⟩
  | binary op a b ia ib =>
    let va := RationalDataflow.evaluate (a.instructions s) v
    have hb : b.Safe va := (b.safe_congr s he.2 va v
      (fun i hi => instructions_frame a s v i (Or.inl hi))).mpr hs.2
    rw [instructions,admissibleTrace_append,admissibleTrace_append]
    exact ⟨⟨ia s he.1 v hs.1,ib (s+a.slots) (he.2.mono (by omega)) va hb⟩,trivial,trivial⟩
  | inverse a ih =>
    rw [instructions,admissibleTrace_append]
    refine ⟨ih s he v hs.1,?_,trivial⟩
    change (RationalDataflow.evaluate (a.instructions s) v (a.output s)).value≠0
    rw [instructions_result a s he v]
    exact hs.2

theorem widthTrace_final (S : Finset ℕ) (B : ℕ) (ins : List Instruction) (v : ℕ → Parts)
    (h : RationalDataflow.WidthTrace S B ins v) : WidthBank S B (RationalDataflow.evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact h
  | cons a rest ih => exact ih (a.update v) h.2.2

theorem instructions_widthTrace (e : RationalExpression) (s : ℕ) (he : e.Below s)
    (S : Finset ℕ) (B : ℕ) (v : ℕ → Parts) (hv : WidthBank S B v) (hw : e.NodeWidths B v) :
    RationalDataflow.WidthTrace S B (e.instructions s) v := by
  induction e generalizing s v with
  | input i => exact hv
  | zero => exact ⟨hv,hw,hv.update s hw⟩
  | binary op a b ia ib =>
    let va := RationalDataflow.evaluate (a.instructions s) v
    let vb := RationalDataflow.evaluate (b.instructions (s+a.slots)) va
    have ha := ia s he.1 v hv hw.2.1
    have hva : WidthBank S B va := widthTrace_final S B _ v ha
    have hbw : b.NodeWidths B va := (b.nodeWidths_congr s B he.2 va v
      (fun i hi => instructions_frame a s v i (Or.inl hi))).mpr hw.2.2
    have hb := ib (s+a.slots) (he.2.mono (by omega)) va hva hbw
    have hvb : WidthBank S B vb := widthTrace_final S B _ va hb
    have hkeep : vb (a.output s)=va (a.output s) :=
      instructions_frame b (s+a.slots) va (a.output s) (Or.inl (output_lt a s he.1))
    have hbe : b.evaluate va=b.evaluate v := b.evaluate_congr s he.2 va v
      (fun i hi => instructions_frame a s v i (Or.inl hi))
    have hresult : (op.eval (vb (a.output s)) (vb (b.output (s+a.slots)))).Width B := by
      have har := instructions_result a s he.1 v
      have hbr := instructions_result b (s+a.slots) (he.2.mono (by omega)) va
      change va (a.output s)=a.evaluate v at har
      change vb (b.output (s+a.slots))=b.evaluate va at hbr
      rw [hkeep,har,hbr,hbe]
      exact hw.1
    rw [instructions,RationalDataflow.widthTrace_append,RationalDataflow.widthTrace_append]
    simp only [RationalDataflow.evaluate_append]
    refine ⟨⟨ha,hb⟩,hvb,trivial,?_⟩
    exact hvb.update _ hresult
  | inverse a ih =>
    let va := RationalDataflow.evaluate (a.instructions s) v
    have ha := ih s he v hv hw.2
    have hva : WidthBank S B va := widthTrace_final S B _ v ha
    have hresult : (va (a.output s)).inverse.Width B := by
      change (RationalDataflow.evaluate (a.instructions s) v (a.output s)).inverse.Width B
      rw [instructions_result a s he v]
      exact hw.1
    rw [instructions,RationalDataflow.widthTrace_append]
    exact ⟨ha,hva,trivial,hva.update _ hresult⟩

#print axioms instructions_result
#print axioms instructions_widthTrace

end Maxwell.Continuum.Calibration.RationalExpression
