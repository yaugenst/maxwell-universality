import Maxwell.Continuum.CalibrationRootGridLoop

/-! The final normalization is executed from the stored grid cube.
The output is the exact rational coefficient used by the analytic error proof. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def coefficientInputs : Finset ℕ := sumInputs∪{12}
def scaleSum : Control := Control.prepend [.binary .mul 10 10 12,.binary .mul 11 11 12] .done
def finishValues (grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  scaleSum.evaluate (Function.update v 12 (FractionWord.part 1 (grid^3)))
def finishCode : Code := .seq (FractionWord.code 344 343 12) scaleSum.code

theorem factor_value (grid : ℕ) : (FractionWord.part 1 (grid^3)).value=((grid:ℚ)^3)⁻¹ := by
  simp [FractionWord.part,Parts.value]

theorem scaleSum_valid (S : Finset ℕ) (hS : coefficientInputs⊆S) : scaleSum.Valid S := by
  have h10 := hS (show 10∈coefficientInputs by decide)
  have h11 := hS (show 11∈coefficientInputs by decide)
  have h12 := hS (show 12∈coefficientInputs by decide)
  simp [scaleSum,Control.prepend,Control.Valid,Instruction.Valid,h10,h11,h12]

theorem scaleSum_admissible (v : ℕ→Parts) : scaleSum.AdmissibleTrace v := by
  simp [scaleSum,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]

theorem scaleSum_literals (W : ℕ) : scaleSum.LiteralsFit W := by
  simp [scaleSum,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits]

theorem finishValues_real (grid : ℕ) (v : ℕ→Parts) :
    (finishValues grid v 10).value=((grid:ℚ)^3)⁻¹*(v 10).value := by
  simp only [finishValues,scaleSum,Control.prepend,List.foldr_cons,List.foldr_nil,
    Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
    Function.update_of_ne (by decide : (10:ℕ)≠11),Function.update_of_ne (by decide : (10:ℕ)≠12)]
  rw [Parts.mul_value,factor_value,mul_comm]

theorem finishValues_imag (grid : ℕ) (v : ℕ→Parts) :
    (finishValues grid v 11).value=((grid:ℚ)^3)⁻¹*(v 11).value := by
  simp only [finishValues,scaleSum,Control.prepend,List.foldr_cons,List.foldr_nil,
    Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
    Function.update_of_ne (by decide : (11:ℕ)≠10),Function.update_of_ne (by decide : (11:ℕ)≠12),
    Function.update_of_ne (by decide : (12:ℕ)≠10)]
  rw [Parts.mul_value,factor_value,mul_comm]

theorem finishValues_exact {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : LoopState S grid N frequency B I initial 0 s)
    (hzero : (initial 10).value=0 ∧ (initial 11).value=0) :
    (finishValues grid h.parts 10).value=
      (Calibration.rationalRootCoefficient grid (initial 9).value N frequency).re.center ∧
    (finishValues grid h.parts 11).value=
      (Calibration.rationalRootCoefficient grid (initial 9).value N frequency).im.center := by
  have hh := h.final_values
  rw [finishValues_real,finishValues_imag,hh.1,hh.2,hzero.1,hzero.2,zero_add,zero_add]
  exact ⟨rfl,rfl⟩

theorem finish_executes (S : Finset ℕ) (hS : coefficientInputs⊆S) (grid W : ℕ) (hgrid : 0<grid)
    (v : ℕ→Parts) (hw : WidthBank S W v) (hg : Good S v) (hW : 1≤W)
    (hgridW : (grid^3).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (ha : Word s.val 344 1) (hb : Word s.val 343 (grid^3)) :
    ∃cost t,Executes input tape finishCode cost s t ∧ cost≤2^108*(W+3)^2 ∧
      Ready S (finishValues grid v) t ∧ Good S (finishValues grid v) ∧
      WidthBank S (4*(W+1)) (finishValues grid v) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := FractionWord.executes S 344 343 12 (by decide) (by decide)
    (hS (by decide)) 1 (grid^3) W v hw hW (by change 1≤W;exact hW) hgridW input tape s hs ha hb
  have wp : (FractionWord.part 1 (grid^3)).Width W := by
    simp only [Parts.Width,FractionWord.part,show (1:ℕ).bits.length=1 by rfl,
      show (0:ℕ).bits.length=0 by rfl]
    exact ⟨hW,Nat.zero_le W,hgridW⟩
  have w0 := hw.update 12 wp
  have gp : (FractionWord.part 1 (grid^3)).Valid := pow_pos hgrid 3
  have g0 := hg.update 12 gp
  have ht : scaleSum.WidthTrace S (4*(W+1)) (Function.update v 12 (FractionWord.part 1 (grid^3))) := by
    simpa only [show scaleSum.steps=2 by rfl,show 2^2=4 by rfl] using
      scaleSum.automatic_widthTrace S (scaleSum_valid S hS) _ W w0 (scaleSum_literals W)
  obtain ⟨c1,t,e1,h1,b1,f1⟩ := scaleSum.executes S (scaleSum_valid S hS) _ (4*(W+1)) ht
    g0 (scaleSum_admissible _) input tape s0 b0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,scaleSum.evaluate_good S (scaleSum_valid S hS) _ g0
    (scaleSum_admissible _),ht.result,f0.trans f1⟩
  have ho : operationCost (4*(W+1))≤2^104*(W+3)^2 := by
    calc
      _≤2^100*(4*(W+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  have hsq : 1≤(W+3)^2 := one_le_pow₀ (by omega)
  change c1≤2*operationCost (4*(W+1))+1 at h1
  nlinarith only [h0,h1,ho,hsq]

#print axioms finishValues_exact
#print axioms finish_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
