import Maxwell.Continuum.CalibrationRootGridCenter

/-! Fixed-code centering and scaling of the three stored grid fractions. -/
namespace Maxwell.Continuum.RationalDataflow.RootGridCenter
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def stageWidth (W : ℕ) : ℕ := 32*(W+1)
def workWidth (W : ℕ) : ℕ := 2^18*(W+2)

theorem center_executes (S : Finset ℕ) (hS : inputs⊆S) (i : Fin 3) (v : ℕ→Parts)
    (W : ℕ) (hW : 2≤W) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape (center i).code cost s t ∧ cost≤5*operationCost (stageWidth W)+1 ∧
      Ready S ((center i).evaluate v) t ∧ Good S ((center i).evaluate v) ∧
      WidthBank S (stageWidth W) ((center i).evaluate v) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have hv := center_valid S hS i
  have ha := center_admissible i v
  have ht : (center i).WidthTrace S (stageWidth W) v := by
    simpa only [center_steps,stageWidth,show 2^5=32 by rfl] using
      (center i).automatic_widthTrace S hv v W hw (center_literals i W hW)
  obtain ⟨c,t,e,hc,hr,hf⟩ := (center i).executes S hv v (stageWidth W) ht hg ha input tape s hs
  exact ⟨c,t,e,by simpa only [center_steps] using hc,hr,
    (center i).evaluate_good S hv v hg ha,ht.result,hf⟩

theorem scale_valid (S : Finset ℕ) (hS : inputs⊆S) : scale.Valid S := by
  have h0 := hS (show 0∈inputs by decide)
  have h1 := hS (show 1∈inputs by decide)
  have h2 := hS (show 2∈inputs by decide)
  have h9 := hS (show 9∈inputs by decide)
  simp [scale,Control.prepend,Control.Valid,Instruction.Valid,h0,h1,h2,h9]
theorem scale_admissible (v : ℕ→Parts) : scale.AdmissibleTrace v := by
  simp [scale,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]
theorem scale_literals (W : ℕ) : scale.LiteralsFit W := by
  simp [scale,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits]
theorem scale_steps : scale.steps=3 := rfl

theorem executes (S : Finset ℕ) (hS : inputs⊆S) (v : ℕ→Parts)
    (W : ℕ) (hW : 2≤W) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^145*(W+3)^2 ∧
      Ready S (values v) t ∧ Good S (values v) ∧ WidthBank S (workWidth W) (values v) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,g0,w0,f0⟩ := center_executes S hS 0 v W hW hw hg input tape s hs
  have hW1 : 2≤stageWidth W := by unfold stageWidth;omega
  obtain ⟨c1,s1,e1,h1,b1,g1,w1,f1⟩ := center_executes S hS 1 (first v) (stageWidth W) hW1 w0 g0 input tape s0 b0
  have hW2 : 2≤stageWidth (stageWidth W) := by unfold stageWidth;omega
  obtain ⟨c2,s2,e2,h2,b2,g2,w2,f2⟩ := center_executes S hS 2 (second v) (stageWidth (stageWidth W)) hW2 w1 g1 input tape s1 b1
  let U := stageWidth (stageWidth (stageWidth W))
  have ht : scale.WidthTrace S (8*(U+1)) (centered v) := by
    simpa only [scale_steps,show 2^3=8 by rfl] using
      scale.automatic_widthTrace S (scale_valid S hS) (centered v) U w2 (scale_literals U)
  obtain ⟨c3,t,e3,h3,b3,f3⟩ := scale.executes S (scale_valid S hS) (centered v) (8*(U+1)) ht
    g2 (scale_admissible _) input tape s2 b2
  have hbound : 8*(U+1)≤workWidth W := by dsimp [U,stageWidth,workWidth];omega
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,
    scale.evaluate_good S (scale_valid S hS) _ g2 (scale_admissible _),ht.result.mono hbound,
    f0.trans (f1.trans (f2.trans f3))⟩
  have hp (B : ℕ) (hb : B+3≤2^18*(W+3)) : operationCost B≤2^136*(W+3)^2 := by
    calc
      _≤2^100*(2^18*(W+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
      _=_ := by ring
  have ha := hp (stageWidth W) (by unfold stageWidth;omega)
  have hb := hp (stageWidth (stageWidth W)) (by unfold stageWidth;omega)
  have hc := hp U (by dsimp [U,stageWidth];omega)
  have hd := hp (8*(U+1)) (by dsimp [U,stageWidth];omega)
  have hsq : 1≤(W+3)^2 := one_le_pow₀ (by omega)
  simp only [scale_steps] at h3
  nlinarith only [h0,h1,h2,h3,ha,hb,hc,hd,hsq]

#print axioms executes
end Maxwell.Continuum.RationalDataflow.RootGridCenter
