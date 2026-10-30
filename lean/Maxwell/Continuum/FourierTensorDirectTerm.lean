import Maxwell.Continuum.FourierTensorWaveAxes
import Maxwell.Continuum.FourierTensorMachineWidths

/-! Direct tensor contraction from the three factors produced in the shared
bank.  The growing sum has its own register outside the phase operand bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def termBank : Finset ℕ := insert 32 tensorBank

def termInstructions : List Instruction :=
  [.binary .mul 0 25 27,
   .binary .mul 1 26 28,
   .binary .sub 2 0 1,
   .binary .mul 0 25 28,
   .binary .mul 1 26 27,
   .binary .add 3 0 1,
   .binary .mul 0 2 29,
   .binary .mul 1 3 30,
   .binary .sub 4 0 1,
   .binary .mul 0 2 30,
   .binary .mul 1 3 29,
   .binary .add 5 0 1,
   .binary .mul 0 23 4,
   .binary .mul 1 24 5,
   .binary .sub 6 0 1,
   .binary .add 32 32 6]

def termBody : Control := Control.done.prepend termInstructions

def tensorTerm (v : ℕ→ℚ) : ℚ :=
  TensorMachine.realProduct (v 23,v 24) (v 25,v 26) (v 27,v 28) (v 29,v 30)

theorem termBody_valid : termBody.Valid termBank := by
  simp [termBody,termInstructions,Control.prepend,Control.Valid,Instruction.Valid,
    termBank,tensorBank,ids]

theorem termBody_rational (v : ℕ→ℚ) :
    termBody.rationalEvaluate v 32=v 32+tensorTerm v := by
  simp [termBody,termInstructions,Control.prepend,Control.rationalEvaluate,
    Instruction.rationalUpdate,tensorTerm,TensorMachine.realProduct]

def termSafeInput (v : ℕ→Parts) (i : ℕ) : Parts :=
  if (23 ≤ i ∧ i ≤ 30) ∨ i=32 then v i else Parts.literal 0

theorem termBody_value (v : ℕ→Parts)
    (hi : ∀i,23 ≤ i → i ≤ 30 → (v i).Valid) (ha : (v 32).Valid) :
    (termBody.evaluate v 32).value=(v 32).value+tensorTerm (valueBank v) := by
  have hg : Good termBank (termSafeInput v) := by
    intro i _
    unfold termSafeInput
    split_ifs with h
    · rcases h with h|rfl
      · exact hi i h.1 h.2
      · exact ha
    · exact Parts.literal_valid 0
  have hv := congrFun (termBody.evaluate_value termBank termBody_valid
    (termSafeInput v) hg (by trivial)) 32
  have he : termBody.evaluate (termSafeInput v) 32=termBody.evaluate v 32 := by
    simp [termBody,termInstructions,Control.prepend,Control.evaluate,
      Instruction.update,termSafeInput]
  change (termBody.evaluate (termSafeInput v) 32).value=_ at hv
  rw [he] at hv
  exact hv.trans (by
    rw [termBody_rational]
    simp [tensorTerm,valueBank,termSafeInput])

theorem termBody_high (v : ℕ→Parts) (i : ℕ) (hi : 7 ≤ i) (hi32 : i≠32) :
    termBody.evaluate v i=v i := by
  simp [termBody,termInstructions,Control.prepend,Control.evaluate,
    Instruction.update,show i≠0 by omega,
    show i≠1 by omega,show i≠2 by omega,show i≠3 by omega,
    show i≠4 by omega,show i≠5 by omega,show i≠6 by omega,hi32]

def termRegisterBounds (A W : ℕ) (i : ℕ) : ℕ :=
  if 23 ≤ i ∧ i ≤ 30 then W else A

theorem termInstructions_width (A W : ℕ) :
    programWidth termInstructions (termRegisterBounds A W) ≤ A+22*W+22 := by
  simp [programWidth,termInstructions,Instruction.resultWidth,Instruction.widthUpdate,
    termRegisterBounds]
  omega

private theorem termTrace_result {S : Finset ℕ} {B : ℕ} (ins : List Instruction) (v : ℕ→Parts)
    (h : RationalDataflow.WidthTrace S B ins v) :
    WidthBank S B (RationalDataflow.evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact h
  | cons a rest ih => exact ih (a.update v) h.2.2

theorem termBody_widthTrace (v : ℕ→Parts) (A W : ℕ)
    (hv : WidthBank termBank A v) (hi : ∀i,23 ≤ i → i ≤ 30 → (v i).Width W) :
    termBody.WidthTrace termBank (A+22*W+22) v := by
  have hvar : RegisterWidths termBank (termRegisterBounds A W) v := by
    intro i him
    by_cases hx : 23 ≤ i ∧ i ≤ 30
    · simpa only [termRegisterBounds,ite_eq_left hx] using hi i hx.1 hx.2
    · simpa only [termRegisterBounds,ite_eq_right hx] using hv i him
  have hvalid : ∀a∈termInstructions,a.Valid termBank := by
    simp [termInstructions,Instruction.Valid,termBank,tensorBank,ids]
  have ht := inferred_widthTrace termBank termInstructions hvalid
    (termRegisterBounds A W) v hvar (A+22*W+22) (hv.mono (by omega))
    (termInstructions_width A W)
  exact Control.prepend_widthTrace termBank termInstructions Control.done v
    (A+22*W+22) ht (termTrace_result termInstructions v ht)

def termCost (A W : ℕ) : ℕ := 16*operationCost (A+22*W+22)+1

theorem term_executes (v : ℕ→Parts) (A W : ℕ) (hv : WidthBank termBank A v)
    (hi : ∀i,23 ≤ i → i ≤ 30 → (v i).Width W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready termBank v s) :
    ∃cost t,Executes input tape termBody.code cost s t ∧ cost ≤ termCost A W ∧
      Ready termBank (termBody.evaluate v) t ∧
      WidthBank termBank (A+22*W+22) (termBody.evaluate v) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val := by
  have ht := termBody_widthTrace v A W hv hi
  have hvalid : ∀a∈termInstructions,a.Valid termBank := by
    simp [termInstructions,Instruction.Valid,termBank,tensorBank,ids]
  have hlist : RationalDataflow.WidthTrace termBank (A+22*W+22) termInstructions v := by
    exact ht
  obtain ⟨cost,t,he,hc,hr,hf⟩ := program_executes termBank termInstructions hvalid v
    (A+22*W+22) hlist input tape s hs
  exact ⟨cost,t,he,hc,hr,ht.result,hf⟩

#print axioms termBody_value
#print axioms termBody_widthTrace
#print axioms term_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
