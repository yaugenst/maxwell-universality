import Maxwell.Continuum.CalibrationCentralTest
import Maxwell.Continuum.CalibrationRawFreeMachine

/-! The actual central/noncentral decision and both free-block branches
run in one fixed rational control program. No supplied branch flag or
reciprocal nonzero certificate is needed in the final execution theorem. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def coordinates (v : ℕ → Parts) : Fin 3 → Parts := ![v 13,v 14,v 15]

def centralInstructions : List Instruction :=
  [.literal 20 1,.binary .add 21 13 20,.binary .mul 21 13 21,.binary .mul 21 21 21,
   .binary .add 22 14 20,.binary .mul 22 14 22,.binary .mul 22 22 22,.binary .add 21 21 22,
   .binary .add 22 15 20,.binary .mul 22 15 22,.binary .mul 22 22 22,.binary .add 21 21 22]

def centralAfter (v : ℕ → Parts) : ℕ → Parts := RationalDataflow.evaluate centralInstructions v

theorem centralAfter_keep (v : ℕ → Parts) (i : ℕ) (hi : i<20) : centralAfter v i=v i := by
  simp [centralAfter,centralInstructions,RationalDataflow.evaluate,Instruction.update,
    show i≠20 by omega,show i≠21 by omega,show i≠22 by omega]

theorem centralAfter_one (v : ℕ → Parts) : centralAfter v 20=Parts.literal 1 := by
  simp [centralAfter,centralInstructions,RationalDataflow.evaluate,Instruction.update]

theorem centralAfter_metric (v : ℕ → Parts) : centralAfter v 21=centralMetric (coordinates v) := by
  simp [centralAfter,centralInstructions,RationalDataflow.evaluate,Instruction.update,
    BinaryOp.eval,centralMetric,sumThree,coordinates]

theorem centralAfter_directions (v : ℕ → Parts) : directions (centralAfter v)=directions v := by
  funext k
  fin_cases k <;> simp [directions,centralAfter_keep]

def freeTail : Control := .positive 21 entryControl (.step (.binary .mul 12 7 20) .done)
def freeControl : Control := freeTail.prepend centralInstructions
def freeRegisters : Finset ℕ := Finset.range 23

theorem freeControl_valid : freeControl.Valid freeRegisters := by
  simp [freeControl,freeTail,centralInstructions,entryControl,entryInstructions,
    Control.prepend,Control.Valid,Instruction.Valid,freeRegisters]

theorem freeControl_steps : freeControl.steps=29 := by decide

theorem freeControl_admissible (v : ℕ → Parts) (hE : (v 1).value≠0)
    (hd : 0<(centralMetric (coordinates v)).value →
      (denominator (v 0) (v 1) (directions v)).value≠0) : freeControl.AdmissibleTrace v := by
  apply Control.prepend_admissibleTrace
  · simp [centralInstructions,RationalDataflow.AdmissibleTrace,Instruction.Admissible]
  · change freeTail.AdmissibleTrace (centralAfter v)
    simp only [freeTail,Control.AdmissibleTrace,centralAfter_metric]
    split_ifs with hp
    · apply entryControl_admissible
      · simpa only [centralAfter_keep v 1 (by decide)] using hE
      · simpa only [centralAfter_keep v 0 (by decide),centralAfter_keep v 1 (by decide),
          centralAfter_directions] using hd hp
    · trivial

theorem freeControl_output (v : ℕ → Parts) (i j : Fin 3)
    (hi : v 5=directions v i) (hj : v 6=directions v j)
    (hδ : v 7=Parts.literal (if i=j then 1 else 0)) :
    freeControl.evaluate v 12 = if 0<(centralMetric (coordinates v)).value then
      entry (v 0) (v 1) (directions v) i j else (v 7).mul (Parts.literal 1) := by
  rw [freeControl,Control.prepend_evaluate]
  change freeTail.evaluate (centralAfter v) 12= _
  simp only [freeTail,Control.evaluate,centralAfter_metric]
  split_ifs
  · rw [entryControl_output _ i j]
    · simp only [centralAfter_keep v 0 (by decide),centralAfter_keep v 1 (by decide),
        centralAfter_directions]
    · simpa only [centralAfter_keep v 5 (by decide),centralAfter_directions] using hi
    · simpa only [centralAfter_keep v 6 (by decide),centralAfter_directions] using hj
    · simpa only [centralAfter_keep v 7 (by decide)] using hδ
  · simp only [Instruction.update,Function.update_self,BinaryOp.eval,centralAfter_one,
      centralAfter_keep v 7 (by decide)]

theorem freeControl_trace (v : ℕ → Parts) (B : ℕ) (hB : 1≤B)
    (hv : WidthBank freeRegisters B v) :
    freeControl.WidthTrace freeRegisters (2^29*(B+1)) v := by
  apply freeControl.automatic_widthTrace freeRegisters freeControl_valid v B hv ?_ |>
    (by simpa only [freeControl_steps] using ·)
  norm_num [freeControl,freeTail,centralInstructions,entryControl,entryInstructions,Control.prepend,
    Control.LiteralsFit,Instruction.LiteralFits,Parts.Width,Parts.literal]
  exact hB

def freeCost (B : ℕ) : ℕ := 29*operationCost (2^29*(B+1))+1

theorem freeCost_bound (B : ℕ) : freeCost B ≤ 2^180*(B+3)^2 := by
  have h : 2^29*(B+1)+3 ≤ 2^29*(B+3) := by omega
  have hs := Nat.pow_le_pow_left h 2
  dsimp [freeCost,operationCost]
  nlinarith only [hs,Nat.zero_le ((B+3)^2)]

theorem actual_free_executes (v : ℕ → Parts) (B : ℕ) (hB : 1≤B)
    (hv : WidthBank freeRegisters B v) (hg : Good freeRegisters v)
    (r : Fin 3 → ℚ) (ν : Alias)
    (hcoord : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hadir : ∀ k, (directions v k).value=rationalDirection r ν k)
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |(r k : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : v 5=directions v i) (hj : v 6=directions v j)
    (hδ : v 7=Parts.literal (if i=j then 1 else 0))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready freeRegisters v s) :
    ∃ cost t, Executes input tape freeControl.code cost s t ∧ cost ≤ freeCost B ∧
      Ready freeRegisters (freeControl.evaluate v) t ∧
      (freeControl.evaluate v 12).Valid ∧
      (freeControl.evaluate v 12).value=rationalFreeInverseMatrix (v 0).value (v 1).value r ν i j ∧
      BinaryPrecision.Frame (workspace freeRegisters) s.val t.val := by
  have ht := hg 0 (by decide)
  have hE := hg 1 (by decide)
  have ha (k : Fin 3) : (directions v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hc (k : Fin 3) : (coordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hEn : (v 1).value≠0 := by
    intro hz
    have hh := hEbox.1
    rw [hz,Rat.cast_zero] at hh
    norm_num at hh
  have branch := centralMetric_pos (coordinates v) hc ν hcoord
  have hd (hp : 0<(centralMetric (coordinates v)).value) :
      (denominator (v 0) (v 1) (directions v)).value≠0 := by
    rw [denominator_value _ _ _ ht hE ha]
    simp_rw [hadir]
    exact (actual_denominator_pos (v 0).value (v 1).value r ν htbox hEbox.2 hrbox (branch.mp hp)).ne'
  have admissible := freeControl_admissible v hEn hd
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := freeControl.executes freeRegisters freeControl_valid v _
    (freeControl_trace v B hB hv) hg admissible input tape s hs
  have good := freeControl.evaluate_good freeRegisters freeControl_valid v hg admissible
  refine ⟨cost,t,he,by simpa only [freeControl_steps,freeCost] using hcost,
    ready,good 12 (by decide),?_,frame⟩
  rw [freeControl_output v i j hi hj hδ]
  by_cases hcentral : IsCentralAlias ν
  · have hneg : ¬0<(centralMetric (coordinates v)).value := fun h => branch.mp h hcentral
    have hcheck := (rationalCentralCheck_true ν).mpr hcentral
    simp only [hneg,ite_false,Parts.mul_value,hδ,Parts.literal_value,mul_one,
      rationalFreeInverseMatrix,hcheck,ite_true,Matrix.one_apply]
  · have hpos := branch.mpr hcentral
    rw [ite_eq_left hpos]
    exact (actual_entry (v 0) (v 1) (directions v) r ν ht hE ha hadir htbox hEbox hrbox hcentral i j).2

#print axioms actual_free_executes

end Maxwell.Continuum.Calibration.RawFree
