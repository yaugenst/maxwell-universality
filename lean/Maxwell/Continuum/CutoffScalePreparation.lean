import Maxwell.Continuum.CutoffAntiderivativeMapWidths
import Maxwell.Continuum.RationalDataflowBankCongruence

/-! Literal shared-register initialization and the simultaneous power/odd
recurrence used to prepare the finite antiderivative conversion. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem literal_nat_parts (n : ℕ) : Parts.literal (n:ℚ)=⟨n,0,1⟩ := by
  simp [Parts.literal]

theorem literal_nat_add (m n : ℕ) : (Parts.literal (m:ℚ)).add (Parts.literal (n:ℚ))=
    Parts.literal ((m+n:ℕ):ℚ) := by
  simp only [literal_nat_parts,Parts.add,mul_one,add_zero]

def scalePrepareInitial : Control := Control.done.prepend
  [.literal 0 0,.literal 1 0,.literal 2 1,.literal 3 1,.literal 4 4,.literal 5 (1/4),.literal 6 2]

def scalePrepareBody : Control :=
  .step (.binary .mul 2 2 4) (.step (.binary .add 3 3 6) .done)

def scalePrepareState (k : ℕ) (v : ℕ→Parts) : ℕ→Parts := fun i =>
  if i=0 then Parts.literal 0 else if i=1 then Parts.literal 0
  else if i=2 then power (Parts.literal 4) k else if i=3 then Parts.literal ((2*k+1:ℕ):ℚ)
  else if i=4 then Parts.literal 4 else if i=5 then Parts.literal (1/4)
  else if i=6 then Parts.literal 2 else v i

theorem scalePrepareInitial_valid : scalePrepareInitial.Valid scaleSlots := by
  simp [scalePrepareInitial,Control.prepend,Control.Valid,Instruction.Valid,scaleSlots]

theorem scalePrepareBody_valid : scalePrepareBody.Valid scaleSlots := by
  simp [scalePrepareBody,Control.Valid,Instruction.Valid,scaleSlots]

theorem scalePrepareInitial_state (v : ℕ→Parts) : scalePrepareInitial.evaluate v=scalePrepareState 0 v := by
  funext i
  by_cases h0 : i=0
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  by_cases h1 : i=1
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  by_cases h2 : i=2
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState,power]
  by_cases h3 : i=3
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  by_cases h4 : i=4
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  by_cases h5 : i=5
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  by_cases h6 : i=6
  · subst i;simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState]
  simp [scalePrepareInitial,Control.prepend,Control.evaluate,Instruction.update,scalePrepareState,
    h0,h1,h2,h3,h4,h5,h6]

theorem scalePrepareBody_state (k : ℕ) (v : ℕ→Parts) :
    scalePrepareBody.evaluate (scalePrepareState k v)=scalePrepareState (k+1) v := by
  funext i
  by_cases h2 : i=2
  · subst i
    simp [scalePrepareBody,Control.evaluate,Instruction.update,BinaryOp.eval,scalePrepareState,power]
  by_cases h3 : i=3
  · subst i
    simp only [scalePrepareBody,Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
      Function.update_of_ne (by decide : (3:ℕ)≠2),Function.update_of_ne (by decide : (6:ℕ)≠2)]
    simp only [scalePrepareState,ite_true,ite_eq_right (by decide : (3:ℕ)≠0),
      ite_eq_right (by decide : (3:ℕ)≠1),ite_eq_right (by decide : (3:ℕ)≠2),
      ite_eq_right (by decide : (6:ℕ)≠0),ite_eq_right (by decide : (6:ℕ)≠1),
      ite_eq_right (by decide : (6:ℕ)≠2),ite_eq_right (by decide : (6:ℕ)≠3),
      ite_eq_right (by decide : (6:ℕ)≠4),ite_eq_right (by decide : (6:ℕ)≠5)]
    rw [show (2:ℚ)=((2:ℕ):ℚ) from rfl,literal_nat_add]
    congr 2
  simp only [scalePrepareBody,Control.evaluate,Instruction.update,
    Function.update_of_ne h2,Function.update_of_ne h3]
  simp only [scalePrepareState,ite_eq_right h2,ite_eq_right h3]

theorem scalePrepare_iterate (k : ℕ) (v : ℕ→Parts) :
    iterateControl scalePrepareBody (scalePrepareState 0 v) k=scalePrepareState k v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterateControl,ih,scalePrepareBody_state]

theorem scalePrepareState_good (k : ℕ) (v : ℕ→Parts) : Good scaleSlots (scalePrepareState k v) := by
  intro i hi
  simp only [scaleSlots,Finset.mem_range] at hi
  interval_cases i <;> simp only [scalePrepareState,ite_true] <;>
    first | exact Parts.literal_valid _ | exact power_valid _ (Parts.literal_valid _) _

theorem scalePrepareState_width (n k : ℕ) (hk : k≤n) (v : ℕ→Parts) :
    WidthBank scaleSlots (8*(n+1)) (scalePrepareState k v) := by
  intro i hi
  simp only [scaleSlots,Finset.mem_range] at hi
  interval_cases i <;> simp only [scalePrepareState,ite_true]
  · exact (Parts.literal_width RationalWords.width_zero').mono (by omega)
  · exact (Parts.literal_width RationalWords.width_zero').mono (by omega)
  · exact (power_width (x:=Parts.literal 4) (B:=3) (by unfold Parts.Width Parts.literal;decide) k).mono (by omega)
  · exact (Parts.literal_width (RationalWords.width_nat (2*k+1))).mono (by omega)
  · exact (show (Parts.literal 4).Width 3 by unfold Parts.Width Parts.literal;decide).mono (by omega)
  · exact literal_quarter_width.mono (by omega)
  · exact literal_two_width.mono (by omega)

theorem scalePrepareBody_widthTrace (n k : ℕ) (hk : k<n) (v : ℕ→Parts) :
    scalePrepareBody.WidthTrace scaleSlots (64*(n+1))
      (iterateControl scalePrepareBody (scalePrepareState 0 v) k) := by
  rw [scalePrepare_iterate]
  apply (scalePrepareBody.automatic_widthTrace scaleSlots scalePrepareBody_valid
    (scalePrepareState k v) (8*(n+1)) (scalePrepareState_width n k hk.le v)
    (by trivial)).mono
  change 2^2*(8*(n+1)+1)≤64*(n+1)
  omega

theorem scalePrepare_finish (n : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i∈scaleSlots) :
    Function.update (scalePrepareState (n-1) v) 4 (Parts.literal 0) i=scaleInitial n i := by
  simp only [scaleSlots,Finset.mem_range] at hi
  interval_cases i <;> simp [scalePrepareState,scaleInitial,descendingPower,descendingOdd]

#print axioms scalePrepareBody_widthTrace
#print axioms scalePrepare_finish
end Maxwell.Continuum.Calibration.RawCutoff
