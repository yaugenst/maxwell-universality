import Maxwell.Continuum.CalibrationMatrixEntryControl

/-! Actual bit execution and automatic intermediate widths for the
complete scalar transition-matrix entry evaluator. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem prepend_literals (ins : List Instruction) (tail : Control) (B : ℕ)
    (hi : ∀ a ∈ ins, a.LiteralFits B) (ht : tail.LiteralsFit B) :
    (tail.prepend ins).LiteralsFit B := by
  induction ins with
  | nil => exact ht
  | cons a rest ih => exact ⟨hi a (by simp),ih (fun b hb => hi b (by simp [hb]))⟩

theorem matrixFinish_literals (B : ℕ) (hB : 101≤B) : matrixFinish.LiteralsFit B := by
  change (Parts.literal rationalAmplitude).Width B ∧ True ∧ True ∧ True
  refine ⟨?_,trivial,trivial,trivial⟩
  apply Parts.Width.mono (B:=101) ?_ hB
  norm_num [Parts.Width,Parts.literal,rationalAmplitude]
  decide

theorem matrixControl_literals (B : ℕ) (hB : 101≤B) : matrixControl.LiteralsFit B := by
  have hy : matrixYes.LiteralsFit B := Control.andThen_literals _ _ B
    (indexedFree_literals B (by omega)) (Control.andThen_literals _ _ B
      (neighborSum_literals B (by omega)) (matrixFinish_literals B hB))
  have ht : matrixTail.LiteralsFit B := ⟨hy,by
    change (Parts.literal 0).Width B ∧ True
    constructor
    · norm_num [Parts.Width,Parts.literal]; omega
    · trivial⟩
  apply prepend_literals matrixGuardInstructions matrixTail B ?_ ht
  simp [matrixGuardInstructions,centralInstructions,columnCentralBody,Instruction.LiteralFits,
    Parts.Width,Parts.literal]
  omega

def matrixEntryWidth (B : ℕ) : ℕ := 2^180*(B+1)
def matrixEntryCost (B : ℕ) : ℕ := 180*operationCost (matrixEntryWidth B)+1

theorem matrixEntryCost_bound (B : ℕ) : matrixEntryCost B≤2^500*(B+3)^2 := by
  have h : 2^180*(B+1)+3≤2^180*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [matrixEntryCost,matrixEntryWidth,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem matrixEntry_executes (S : Finset ℕ) (hS : neighborRegisters ⊆ S)
    (v : ℕ → Parts) (B : ℕ) (hB : 101≤B) (hv : WidthBank S B v) (hg : Good S v)
    (ν μ : Alias) (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape matrixControl.code cost s t ∧ cost≤matrixEntryCost B ∧
      Ready S (matrixControl.evaluate v) t ∧ Good S (matrixControl.evaluate v) ∧
      WidthBank S (matrixEntryWidth B) (matrixControl.evaluate v) ∧
      (matrixControl.evaluate v 12).value=stencilEntry (v 0).value (v 1).value
        (fun k => (quasiParts v k).value) ν i μ j ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨admissible,value⟩ := matrixControl_contract v (fun k hk => hg k (hS hk))
    ν μ hν hμ htbox hEbox hrbox i j hi hj
  have valid := matrixControl_valid.mono hS
  have trace : matrixControl.WidthTrace S (matrixEntryWidth B) v := by
    simpa only [matrixControl_steps,matrixEntryWidth] using
      matrixControl.automatic_widthTrace S valid v B hv (matrixControl_literals B hB)
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := matrixControl.executes S valid v _ trace hg admissible input tape s hs
  exact ⟨cost,t,he,by simpa only [matrixEntryCost,matrixControl_steps] using hcost,ready,
    matrixControl.evaluate_good S valid v hg admissible,trace.result,value,frame⟩

#print axioms matrixEntry_executes

end Maxwell.Continuum.Calibration.RawFree
