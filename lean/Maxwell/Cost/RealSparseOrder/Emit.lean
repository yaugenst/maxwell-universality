import Maxwell.Cost.RealSparseOrder.Buffer

/-! One record-copy macro for the actual addressed merge. The Boolean
parameter selects one of two fixed source cursors; record values are read
from machine storage by ordinary load instructions. -/
namespace Maxwell.Cost.RealSparseOrder.Emit
open RealSparse (execute execute_sound)
open RealSimulation.Control

set_option maxRecDepth 20000

def rowRegister (left : Bool) : ℕ := if left then 6 else 8
def valueRegister (left : Bool) : ℕ := if left then 7 else 9
def countRegister (left : Bool) : ℕ := if left then 3 else 4

def program (left : Bool) : Machine := ⟨[
  .loadIndex 13 (rowRegister left),.indexAdd 12 (rowRegister left) 1,.loadIndex 14 12,
  .load 0 (valueRegister left),.storeIndex 10 13,.indexAdd 12 10 1,.storeIndex 12 14,
  .store 11 0,.indexAdd (rowRegister left) (rowRegister left) 2,
  .indexAdd (valueRegister left) (valueRegister left) 1,
  .indexSubtract (countRegister left) (countRegister left) 1,.indexSubtract 5 5 1,
  .indexAdd 10 10 2,.indexAdd 11 11 1,.halt]⟩

noncomputable def head (s : RAMState) (row value : ℕ) : SparseEntry :=
  ⟨s.indices row,s.indices (row+1),s.words value⟩

noncomputable def middle (left : Bool) (s : RAMState) : RAMState :=
  let e := head s (s.indices (rowRegister left)) (s.indices (valueRegister left))
  let t := s.setIndex 13 e.row
  let t := t.setIndex 12 (s.indices (rowRegister left)+1)
  let t := t.setIndex 14 e.column
  let t := t.setWord 0 e.value
  let t := t.setIndex (s.indices 10) e.row
  let t := t.setIndex 12 (s.indices 10+1)
  let t := t.setIndex (s.indices 10+1) e.column
  t.setWord (s.indices 11) e.value

noncomputable def advanced (left : Bool) (s : RAMState) : RAMState :=
  let t := middle left s
  let t := t.setIndex (rowRegister left) (s.indices (rowRegister left)+2)
  let t := t.setIndex (valueRegister left) (s.indices (valueRegister left)+1)
  let t := t.setIndex (countRegister left) (s.indices (countRegister left)-1)
  let t := t.setIndex 5 (s.indices 5-1)
  let t := t.setIndex 10 (s.indices 10+2)
  t.setIndex 11 (s.indices 11+1)

/-- The macro's only address restrictions protect its finite register bank. -/
def Ready (left : Bool) (s : RAMState) : Prop :=
  s.pc=0 ∧ s.indices 1=1 ∧ s.indices 2=2 ∧
    100 ≤ s.indices (rowRegister left) ∧ 100 ≤ s.indices (valueRegister left) ∧
    100 ≤ s.indices 10 ∧ 100 ≤ s.indices 11

set_option maxHeartbeats 1600000 in
private theorem first_steps (left : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hr : Ready left s) :
    execute ((program left).next input tape) 8 s = some (middle left s) := by
  rcases hr with ⟨hpc,h1,h2,hs,hv,ht,hw⟩
  have hsSmall : ∀ j : ℕ, j<17 → s.indices (rowRegister left)≠j := by omega
  have hsNext : ∀ j : ℕ, j<17 → s.indices (rowRegister left)+1≠j := by omega
  have htSmall : ∀ j : ℕ, j<17 → j≠s.indices 10 := by omega
  have htNext : ∀ j : ℕ, j<17 → j≠s.indices 10+1 := by omega
  have htZero : s.indices 10 ≠ 0 := by omega
  cases left <;> simp [rowRegister] at hsSmall hsNext ⊢
  all_goals simp (config := {maxSteps := 150000}) [execute,program,Machine.next,RAMState.setIndex,
    RAMState.setWord,middle,head,rowRegister,valueRegister,hpc,h1,
    hsNext,htSmall,htNext]

set_option maxHeartbeats 1600000 in
private theorem last_steps (left : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hr : Ready left s) :
    execute ((program left).next input tape) 6 (middle left s) = some (advanced left s) := by
  rcases hr with ⟨hpc,h1,h2,hs,hv,ht,hw⟩
  have htSmall : ∀ j : ℕ, j<17 → j≠s.indices 10 := by omega
  have htNext : ∀ j : ℕ, j<17 → j≠s.indices 10+1 := by omega
  have htZero : s.indices 10 ≠ 0 := by omega
  cases left <;> simp (config := {maxSteps := 150000}) [execute,program,Machine.next,RAMState.setIndex,
    RAMState.setWord,advanced,middle,rowRegister,valueRegister,countRegister,hpc,h1,h2,
    htSmall,htNext,htZero]

theorem steps (left : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hr : Ready left s) :
    execute ((program left).next input tape) 14 s = some (advanced left s) := by
  rw [show 14=8+6 from rfl,RealSparse.execute_add,first_steps left input tape s hr,Option.bind_some]
  exact last_steps left input tape s hr

theorem executes (left : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : Store) (hr : Ready left s.val) :
    Executes input tape (.call (program left)) 15 s (Store.ofState (advanced left s.val)) := by
  apply Executes.call _ s _ 14 (execute_sound _ (steps left input tape s.val hr))
  cases left <;> simp [program,advanced,middle,RAMState.setIndex,RAMState.setWord,
    rowRegister,valueRegister,countRegister,hr.1]

/-- Coefficient cells outside the one destination and temporary register are unchanged. -/
theorem words_frame (left : Bool) (s : RAMState) (j : ℕ)
    (h0 : j≠0) (hd : j≠s.indices 11) : (advanced left s).words j=s.words j := by
  simp [advanced,middle,RAMState.setIndex,RAMState.setWord,h0,hd]

/-- Coordinate memory outside the one destination record is unchanged. -/
theorem indices_frame (left : Bool) (s : RAMState) (j : ℕ)
    (hj : 17 ≤ j) (hr : j≠s.indices 10) (hc : j≠s.indices 10+1) :
    (advanced left s).indices j=s.indices j := by
  cases left <;> simp [advanced,middle,RAMState.setIndex,RAMState.setWord,rowRegister,
    valueRegister,countRegister,hr,hc,show j≠3 by omega,show j≠4 by omega,
    show j≠5 by omega,show j≠6 by omega,show j≠7 by omega,show j≠8 by omega,
    show j≠9 by omega,show j≠10 by omega,show j≠11 by omega,show j≠12 by omega,
    show j≠13 by omega,show j≠14 by omega]

end Maxwell.Cost.RealSparseOrder.Emit
