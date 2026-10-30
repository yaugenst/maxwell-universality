import Maxwell.Continuum.CalibrationRawFreeEvaluation
import Maxwell.Continuum.RationalDataflowControlResults

/-! A fixed sixteen-instruction rational circuit for an actual noncentral
free-block entry. Its width and reciprocal contracts are proved here. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def entryInstructions : List Instruction :=
  [.binary .mul 8 2 2,.binary .mul 9 3 3,.binary .add 8 8 9,
   .binary .mul 9 4 4,.binary .add 8 8 9,.binary .mul 9 0 0,
   .binary .mul 8 9 8,.binary .sub 8 8 1,.inverse 8 8,.inverse 9 1,
   .binary .mul 10 0 5,.binary .mul 11 0 6,.binary .mul 10 10 11,
   .binary .mul 10 9 10,.binary .sub 10 7 10,.binary .mul 12 8 10]

def entryControl : Control := Control.done.prepend entryInstructions
def entryRegisters : Finset ℕ := Finset.range 13
def directions (v : ℕ → Parts) : Fin 3 → Parts := ![v 2,v 3,v 4]

theorem entryControl_valid : entryControl.Valid entryRegisters := by
  simp [entryControl,entryInstructions,Control.prepend,Control.Valid,Instruction.Valid,entryRegisters]
theorem entryControl_steps : entryControl.steps = 16 := by decide

theorem entryControl_admissible (v : ℕ → Parts)
    (hE : (v 1).value ≠ 0) (hd : (denominator (v 0) (v 1) (directions v)).value ≠ 0) :
    entryControl.AdmissibleTrace v := by
  simpa [entryControl,entryInstructions,Control.prepend,Control.AdmissibleTrace,
    Instruction.Admissible,Instruction.update,BinaryOp.eval,Function.update_apply,
    denominator,squareSum,directions] using And.intro hd hE

theorem entryControl_output (v : ℕ → Parts) (i j : Fin 3)
    (hi : v 5 = directions v i) (hj : v 6 = directions v j)
    (hδ : v 7 = Parts.literal (if i=j then 1 else 0)) :
    entryControl.evaluate v 12 = entry (v 0) (v 1) (directions v) i j := by
  simp [entryControl,entryInstructions,Control.prepend,Control.evaluate,
    Instruction.update,BinaryOp.eval,entry,denominator,
    squareSum,numerator,directions,hi,hj,hδ]

theorem entryControl_trace (v : ℕ → Parts) (B : ℕ) (hv : WidthBank entryRegisters B v) :
    entryControl.WidthTrace entryRegisters (2^16*(B+1)) v := by
  simpa only [entryControl_steps] using entryControl.automatic_widthTrace entryRegisters
    entryControl_valid v B hv
    (by simp [entryControl,entryInstructions,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits])

def entryCost (B : ℕ) : ℕ := 16*operationCost (2^16*(B+1))+1

theorem entryCost_bound (B : ℕ) : entryCost B ≤ 2^140*(B+3)^2 := by
  have h : 2^16*(B+1)+3 ≤ 2^16*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [entryCost,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem entry_executes (v : ℕ → Parts) (B : ℕ)
    (hv : WidthBank entryRegisters B v) (hg : Good entryRegisters v)
    (hE : (v 1).value ≠ 0) (hd : (denominator (v 0) (v 1) (directions v)).value ≠ 0)
    (i j : Fin 3) (hi : v 5 = directions v i) (hj : v 6 = directions v j)
    (hδ : v 7 = Parts.literal (if i=j then 1 else 0))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready entryRegisters v s) :
    ∃ cost t, Executes input tape entryControl.code cost s t ∧ cost ≤ entryCost B ∧
      Ready entryRegisters (entryControl.evaluate v) t ∧
      entryControl.evaluate v 12 = entry (v 0) (v 1) (directions v) i j ∧
      BinaryPrecision.Frame (workspace entryRegisters) s.val t.val := by
  obtain ⟨cost,t,he,hcost,hr,hf⟩ := entryControl.executes entryRegisters entryControl_valid
    v _ (entryControl_trace v B hv) hg (entryControl_admissible v hE hd) input tape s hs
  exact ⟨cost,t,he,by simpa only [entryControl_steps,entryCost] using hcost,
    hr,entryControl_output v i j hi hj hδ,hf⟩

theorem actual_entry_computes (v : ℕ → Parts) (B : ℕ)
    (hv : WidthBank entryRegisters B v) (hg : Good entryRegisters v)
    (r : Fin 3 → ℚ) (ν : Alias)
    (hadir : ∀ k, (directions v k).value = rationalDirection r ν k)
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hr : ∀ k, |(r k : ℝ)| ≤ 1/16) (hν : ¬IsCentralAlias ν)
    (i j : Fin 3) (hi : v 5 = directions v i) (hj : v 6 = directions v j)
    (hδ : v 7 = Parts.literal (if i=j then 1 else 0))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready entryRegisters v s) :
    ∃ t : Store,
      (runPriced (entryControl.code.compile.next input tape) (entryCost B+1) s.val).finished =
        some (t.place entryControl.code.size) ∧
      (runPriced (entryControl.code.compile.next input tape) (entryCost B+1) s.val).instructions ≤
        2^140*(B+3)^2 ∧
      Ready entryRegisters (entryControl.evaluate v) t ∧
      (entryControl.evaluate v 12).Valid ∧
      (entryControl.evaluate v 12).value = rationalFreeInverseMatrix (v 0).value (v 1).value r ν i j := by
  have ht := hg 0 (by decide)
  have hE := hg 1 (by decide)
  have ha (k : Fin 3) : (directions v k).Valid := by
    fin_cases k <;> exact hg _ (by decide)
  have hEn : (v 1).value ≠ 0 := by
    intro hz
    have h := hEbox.1
    rw [hz,Rat.cast_zero] at h
    norm_num at h
  have hd : (denominator (v 0) (v 1) (directions v)).value ≠ 0 := by
    rw [denominator_value _ _ _ ht hE ha]
    simp_rw [hadir]
    exact (actual_denominator_pos (v 0).value (v 1).value r ν htbox hEbox.2 hr hν).ne'
  obtain ⟨cost,t,he,hcost,hready,hout,_⟩ := entry_executes v B hv hg hEn hd i j hi hj hδ
    input tape s hs
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (entryCost B+1) (by omega)
  have hc := actual_entry (v 0) (v 1) (directions v) r ν ht hE ha hadir htbox hEbox hr hν i j
  exact ⟨t,hrun,hsteps ▸ hcost.trans (entryCost_bound B),hready,hout ▸ hc.1,hout ▸ hc.2⟩

#print axioms actual_entry_computes

end Maxwell.Continuum.Calibration.RawFree
