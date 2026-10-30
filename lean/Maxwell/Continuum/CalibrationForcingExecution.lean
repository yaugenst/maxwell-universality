import Maxwell.Continuum.CalibrationForcingControl

/-! Actual fixed-code forcing evaluation with automatic raw intermediate
widths and charged Boolean execution. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem forcingLoop_steps (js : List (Fin 3)) : (forcingLoop js).steps=52*js.length := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
    simp only [forcingLoop,Control.andThen_steps,forcingTerm,Control.steps,
      indexedFree_steps,forcingFinish,ih,List.length_cons]
    omega

theorem forcingControl_steps : forcingControl.steps=157 := by
  rw [forcingControl,Control.steps,forcingLoop_steps]
  rfl

theorem forcingTerm_literals (j : Fin 3) (B : ℕ) (hB : 2≤B) : (forcingTerm j).LiteralsFit B := by
  constructor
  · apply Parts.Width.mono (B:=2) ?_ hB
    fin_cases j <;> norm_num [Instruction.LiteralFits,Parts.Width,Parts.literal]
    decide
  · exact Control.andThen_literals _ _ B (indexedFree_literals B hB) ⟨trivial,trivial,trivial⟩

theorem forcingLoop_literals (js : List (Fin 3)) (B : ℕ) (hB : 2≤B) :
    (forcingLoop js).LiteralsFit B := by
  induction js with
  | nil => trivial
  | cons j rest ih => exact Control.andThen_literals _ _ B (forcingTerm_literals j B hB) ih

theorem forcingControl_literals (B : ℕ) (hB : 2≤B) : forcingControl.LiteralsFit B := by
  refine ⟨?_,forcingLoop_literals _ B hB⟩
  norm_num [Instruction.LiteralFits,Parts.Width,Parts.literal]
  omega

theorem forcingControl_valid : forcingControl.Valid neighborRegisters :=
  ⟨by change 36∈Finset.range 41; decide,forcingLoop_valid _⟩

def forcingWidth (B : ℕ) : ℕ := 2^157*(B+1)
def forcingCost (B : ℕ) : ℕ := 157*operationCost (forcingWidth B)+1

theorem forcingCost_bound (B : ℕ) : forcingCost B≤2^450*(B+3)^2 := by
  have h : 2^157*(B+1)+3≤2^157*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [forcingCost,forcingWidth,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem forcing_executes (S : Finset ℕ) (hS : neighborRegisters⊆S)
    (v : ℕ→Parts) (B : ℕ) (hB : 2≤B) (hv : WidthBank S B v) (hg : Good S v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16)
    (i : Fin 3) (hi : (v 23).value=(i.val:ℚ))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape forcingControl.code cost s t ∧ cost≤forcingCost B ∧
      Ready S (forcingControl.evaluate v) t ∧ Good S (forcingControl.evaluate v) ∧
      WidthBank S (forcingWidth B) (forcingControl.evaluate v) ∧
      (forcingControl.evaluate v 36).value=∑ j,
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j*
          (forcingSource v j).value ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨admissible,value⟩ := forcingControl_contract v (fun k hk => hg k (hS hk)) ν hν ht hE hr i hi
  have valid := forcingControl_valid.mono hS
  have trace : forcingControl.WidthTrace S (forcingWidth B) v := by
    simpa only [forcingControl_steps,forcingWidth] using
      forcingControl.automatic_widthTrace S valid v B hv (forcingControl_literals B hB)
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := forcingControl.executes S valid v _ trace hg admissible input tape s hs
  exact ⟨cost,t,he,by simpa only [forcingCost,forcingControl_steps] using hcost,ready,
    forcingControl.evaluate_good S valid v hg admissible,trace.result,value,frame⟩

#print axioms forcing_executes

end Maxwell.Continuum.Calibration.RawFree
