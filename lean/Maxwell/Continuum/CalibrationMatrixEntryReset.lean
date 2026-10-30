import Maxwell.Continuum.CalibrationMatrixEntryMachine

/-! Repeated table emission clears nonparameter rational registers with
fixed code. Their widths are reset from the actual parameters at every
entry; no multiplicative width recurrence over the number of entries is used. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def matrixParameters : Finset ℕ := {0,1,16,17,18}
def resetSlots : Finset ℕ := RawFree.neighborRegisters \ matrixParameters
def resetList : List ℕ := (List.range 41).filter (fun k => decide (k∉matrixParameters))
def resetInstructions : List Instruction := resetList.map (fun k => .literal k 0)
def resetCode : Code := RationalDataflow.program resetInstructions
def resetParts (v : ℕ → Parts) (k : ℕ) : Parts := if k∈resetSlots then Parts.literal 0 else v k

theorem zero_list_evaluate (xs : List ℕ) (v : ℕ → Parts) (k : ℕ) :
    RationalDataflow.evaluate (xs.map (fun i => Instruction.literal i 0)) v k=
      if k∈xs then Parts.literal 0 else v k := by
  induction xs generalizing v with
  | nil => simp [RationalDataflow.evaluate]
  | cons a rest ih =>
    rw [List.map_cons,RationalDataflow.evaluate,ih]
    by_cases hr : k∈rest <;> by_cases ha : k=a <;> simp [hr,ha,Instruction.update]

theorem reset_evaluate (v : ℕ → Parts) : RationalDataflow.evaluate resetInstructions v=resetParts v := by
  funext k
  simpa [resetInstructions,resetParts,resetList,resetSlots,RawFree.neighborRegisters] using zero_list_evaluate resetList v k

theorem reset_valid : ∀ a ∈ resetInstructions, a.Valid RawFree.neighborRegisters := by
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  have h : k∈resetSlots := by simpa [resetList,resetSlots,RawFree.neighborRegisters] using hk
  exact (Finset.mem_sdiff.mp h).1

theorem reset_length : resetInstructions.length=36 := by decide

theorem zero_list_trace (xs : List ℕ) (v : ℕ → Parts) (U : ℕ) (hU : 1≤U)
    (hv : WidthBank RawFree.neighborRegisters U v) :
    WidthTrace RawFree.neighborRegisters U (xs.map (fun i => Instruction.literal i 0)) v := by
  induction xs generalizing v with
  | nil => exact hv
  | cons a rest ih =>
    have hz : (Parts.literal 0).Width U := by norm_num [Parts.Width,Parts.literal]; exact hU
    exact ⟨hv,hz,ih (Function.update v a (Parts.literal 0)) (hv.update a hz)⟩

theorem reset_width (v : ℕ → Parts) (B : ℕ) (hB : 1≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B) :
    WidthBank RawFree.neighborRegisters B (resetParts v) := by
  intro k hk
  by_cases hr : k∈resetSlots
  · rw [resetParts,ite_eq_left hr]
    norm_num [Parts.Width,Parts.literal]
    exact hB
  · have hm : k∈matrixParameters := by
      simp only [resetSlots,Finset.mem_sdiff,not_and] at hr
      exact not_not.mp (hr hk)
    rw [resetParts,ite_eq_right hr]
    exact hp k hm

theorem reset_good (v : ℕ → Parts) (hp : ∀ k∈matrixParameters, (v k).Valid) :
    Good RawFree.neighborRegisters (resetParts v) := by
  intro k hk
  by_cases hr : k∈resetSlots
  · rw [resetParts,ite_eq_left hr]
    exact Parts.literal_valid 0
  · have hm : k∈matrixParameters := by
      simp only [resetSlots,Finset.mem_sdiff,not_and] at hr
      exact not_not.mp (hr hk)
    rw [resetParts,ite_eq_right hr]
    exact hp k hm

theorem reset_keeps_parameter (v : ℕ → Parts) (k : ℕ) (hk : k∈matrixParameters) :
    resetParts v k=v k := by simp [resetParts,resetSlots,hk]

theorem reset_executes (v : ℕ → Parts) (U B : ℕ) (hU : 1≤U) (hB : 1≤B)
    (hv : WidthBank RawFree.neighborRegisters U v)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : RationalDataflow.Ready RawFree.neighborRegisters v s) :
    ∃ cost t, Executes input tape resetCode cost s t ∧ cost≤2^107*(U+3)^2 ∧
      RationalDataflow.Ready RawFree.neighborRegisters (resetParts v) t ∧
      WidthBank RawFree.neighborRegisters B (resetParts v) ∧
      Good RawFree.neighborRegisters (resetParts v) ∧
      BinaryPrecision.Frame (workspace RawFree.neighborRegisters) s.val t.val := by
  obtain ⟨cost,t,he,hcost,ready,frame⟩ := program_executes RawFree.neighborRegisters resetInstructions reset_valid
    v U (zero_list_trace resetList v U hU hv) input tape s hs
  rw [reset_evaluate] at ready
  refine ⟨cost,t,he,?_,ready,reset_width v B hB (fun k hk => (hp k hk).1),
    reset_good v (fun k hk => (hp k hk).2),frame⟩
  rw [reset_length] at hcost
  unfold operationCost at hcost
  have hsquare : 1≤(U+3)^2 := one_le_pow₀ (by omega)
  nlinarith only [hcost,hsquare]

#print axioms reset_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
