import Maxwell.Continuum.FourierTensorDirectFrame

/-! Each tensor summand returns a small wave operand bank. Only the
separate, additively growing sum survives the charged scratch erasure. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def termClearInstructions : List Instruction :=
  [.literal 0 0,.literal 1 0,.literal 2 0,.literal 3 0,
    .literal 4 0,.literal 5 0,.literal 6 0]
def termReturned (v : ℕ→Parts) : ℕ→Parts :=
  evaluate termClearInstructions (termBody.evaluate v)
def termReturnCode : Code := .seq termBody.code (program termClearInstructions)
def termReturnCost (A W : ℕ) : ℕ := termCost A W+7*operationCost (A+22*W+23)+1

theorem termReturned_eq (v : ℕ→Parts) (i : ℕ) :
    termReturned v i=if i<7 then Parts.literal 0 else termBody.evaluate v i := by
  by_cases hi : i<7
  · interval_cases i <;> simp [termReturned,termClearInstructions,evaluate,Instruction.update]
  · simp (disch := omega) [termReturned,termClearInstructions,evaluate,Instruction.update,hi]

theorem termReturned_high (v : ℕ→Parts) (i : ℕ) (hi : 7 ≤ i) (hi32 : i≠32) :
    termReturned v i=v i := by
  rw [termReturned_eq,ite_eq_right (by omega),termBody_high v i hi hi32]

theorem termReturned_small_width (v : ℕ→Parts) (W : ℕ) (hW : 1 ≤ W)
    (hw : WidthBank tensorBank W v) : WidthBank tensorBank W (termReturned v) := by
  intro i hi
  by_cases hil : i<7
  · rw [termReturned_eq,ite_eq_left hil]
    exact (show (Parts.literal 0).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · rw [termReturned_high v i (by omega) (by
      intro he;subst i;exact (by decide : 32∉tensorBank) hi)]
    exact hw i hi

theorem termBody_accumulator_valid (v : ℕ→Parts)
    (hi : ∀i,23 ≤ i → i ≤ 30 → (v i).Valid) (ha : (v 32).Valid) :
    (termBody.evaluate v 32).Valid := by
  have hg : Good termBank (termSafeInput v) := by
    intro i _
    unfold termSafeInput
    split_ifs with h
    · rcases h with h|rfl
      · exact hi i h.1 h.2
      · exact ha
    · exact Parts.literal_valid 0
  have hv := termBody.evaluate_good termBank termBody_valid (termSafeInput v) hg (by trivial) 32 (by simp [termBank])
  have he : termBody.evaluate (termSafeInput v) 32=termBody.evaluate v 32 := by
    simp [termBody,termInstructions,Control.prepend,Control.evaluate,Instruction.update,termSafeInput]
  simpa only [he] using hv

theorem termReturned_value (v : ℕ→Parts)
    (hi : ∀i,23 ≤ i → i ≤ 30 → (v i).Valid) (ha : (v 32).Valid) :
    (termReturned v 32).Valid ∧
      (termReturned v 32).value=(v 32).value+tensorTerm (valueBank v) := by
  rw [termReturned_eq,ite_eq_right (by decide : ¬32<7)]
  exact ⟨termBody_accumulator_valid v hi ha,termBody_value v hi ha⟩

private theorem clearTrace_result {S : Finset ℕ} {B : ℕ} (ins : List Instruction) (v : ℕ→Parts)
    (h : WidthTrace S B ins v) : WidthBank S B (evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact h
  | cons a rest ih => exact ih (a.update v) h.2.2

theorem termReturn_executes {n D Q N : ℕ} (a : Table n) (b : Table (2*D))
    (v : ℕ→Parts) (A W : ℕ) (hW : 1 ≤ W) (hw : WidthBank tensorBank W v)
    (hv : WidthBank termBank A v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : FactorReady a Q N b v s) (hr : Ready termBank v s) :
    ∃cost t,Executes input tape termReturnCode cost s t ∧ cost ≤ termReturnCost A W ∧
      FactorReady a Q N b (termReturned v) t ∧ Ready termBank (termReturned v) t ∧
      WidthBank tensorBank W (termReturned v) ∧ (termReturned v 32).Width (A+22*W+23) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val := by
  have hinput (i : ℕ) (hi : 23 ≤ i) (hi' : i ≤ 30) : (v i).Width W :=
    hw i (by simp [tensorBank,Finset.mem_Ico];omega)
  obtain ⟨c0,s0,e0,h0,r0,w0,f0⟩ := term_executes v A W hv hinput input tape s hr
  have hvalid : ∀a∈termClearInstructions,a.Valid termBank := by
    simp [termClearInstructions,Instruction.Valid,termBank,tensorBank,ids]
  have hwidth : programWidth termClearInstructions (fun _ => A+22*W+22) ≤ A+22*W+23 := by
    simp [programWidth,termClearInstructions,Instruction.resultWidth,Parts.literal]
  have htrace := inferred_widthTrace termBank termClearInstructions hvalid
    (fun _ => A+22*W+22) (termBody.evaluate v) w0 (A+22*W+23) (w0.mono (by omega)) hwidth
  obtain ⟨c1,t,e1,h1,r1,f1⟩ := program_executes termBank termClearInstructions hvalid
    (termBody.evaluate v) (A+22*W+23) htrace input tape s0 r0
  have w1 : WidthBank termBank (A+22*W+23) (termReturned v) :=
    clearTrace_result termClearInstructions (termBody.evaluate v) htrace
  have f := f0.trans f1
  refine ⟨c0+c1,t,e0.seq e1,?_,hs.term_frame f r1,r1,
    termReturned_small_width v W hW hw,w1 32 (by simp [termBank]),f⟩
  have hc1 : c1 ≤ 7*operationCost (A+22*W+23)+1 := h1
  unfold termReturnCost
  omega

#print axioms termReturned_value
#print axioms termReturn_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
