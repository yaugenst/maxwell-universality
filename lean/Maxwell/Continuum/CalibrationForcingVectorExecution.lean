import Maxwell.Continuum.CalibrationForcingVector

/-! Charged execution of the three polarization forcing outputs, with a
fixed instruction stream and automatic raw word widths. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem forcingVectorLoop_steps (js : List (Fin 3)) : (forcingVectorLoop js).steps=159*js.length := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
    simp only [forcingVectorLoop,Control.andThen_steps,forcingVectorTerm,Control.steps,
      forcingControl_steps,ih,List.length_cons]
    omega

theorem forcingVectorControl_steps : forcingVectorControl.steps=478 := by
  rw [forcingVectorControl,Control.steps,forcingVectorLoop_steps]
  rfl

theorem forcingVectorTerm_literals (j : Fin 3) (B : ℕ) (hB : 2≤B) :
    (forcingVectorTerm j).LiteralsFit B := by
  constructor
  · apply Parts.Width.mono (B:=2) ?_ hB
    fin_cases j <;> norm_num [Instruction.LiteralFits,Parts.Width,Parts.literal]
    decide
  · exact Control.andThen_literals _ _ B (forcingControl_literals B hB) ⟨trivial,trivial⟩

theorem forcingVectorLoop_literals (js : List (Fin 3)) (B : ℕ) (hB : 2≤B) :
    (forcingVectorLoop js).LiteralsFit B := by
  induction js with
  | nil => trivial
  | cons j rest ih => exact Control.andThen_literals _ _ B (forcingVectorTerm_literals j B hB) ih

theorem forcingVectorControl_literals (B : ℕ) (hB : 2≤B) : forcingVectorControl.LiteralsFit B := by
  refine ⟨?_,forcingVectorLoop_literals _ B hB⟩
  norm_num [Instruction.LiteralFits,Parts.Width,Parts.literal]
  omega

theorem forcingVectorControl_valid : forcingVectorControl.Valid neighborRegisters :=
  ⟨by change 40∈Finset.range 41; decide,forcingVectorLoop_valid _⟩

def forcingVectorWidth (B : ℕ) : ℕ := 2^478*(B+1)
def forcingVectorCost (B : ℕ) : ℕ := 478*operationCost (forcingVectorWidth B)+1

theorem forcingVectorCost_bound (B : ℕ) : forcingVectorCost B≤2^1100*(B+3)^2 := by
  have h : 2^478*(B+1)+3≤2^478*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [forcingVectorCost,forcingVectorWidth,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem forcingVector_executes (S : Finset ℕ) (hS : neighborRegisters⊆S)
    (v : ℕ→Parts) (B : ℕ) (hB : 2≤B) (hv : WidthBank S B v) (hg : Good S v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape forcingVectorControl.code cost s t ∧ cost≤forcingVectorCost B ∧
      Ready S (forcingVectorControl.evaluate v) t ∧ Good S (forcingVectorControl.evaluate v) ∧
      WidthBank S (forcingVectorWidth B) (forcingVectorControl.evaluate v) ∧
      (∀ i : Fin 3, (forcingVectorControl.evaluate v (37+i.val)).value=forcingCoefficient v ν i) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨admissible,value⟩ := forcingVectorControl_contract v (fun k hk => hg k (hS hk)) ν hν ht hE hr
  have valid := forcingVectorControl_valid.mono hS
  have trace : forcingVectorControl.WidthTrace S (forcingVectorWidth B) v := by
    simpa only [forcingVectorControl_steps,forcingVectorWidth] using
      forcingVectorControl.automatic_widthTrace S valid v B hv (forcingVectorControl_literals B hB)
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := forcingVectorControl.executes S valid v _ trace hg admissible input tape s hs
  exact ⟨cost,t,he,by simpa only [forcingVectorCost,forcingVectorControl_steps] using hcost,ready,
    forcingVectorControl.evaluate_good S valid v hg admissible,trace.result,value,frame⟩

#print axioms forcingVector_executes

end Maxwell.Continuum.Calibration.RawFree
