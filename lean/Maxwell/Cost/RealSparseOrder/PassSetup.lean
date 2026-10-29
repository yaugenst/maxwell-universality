import Maxwell.Cost.RealSparseOrder.MergeState
import Maxwell.Cost.RealSparseOrder.DataFrame

namespace Maxwell.Cost.RealSparseOrder.PassSetup
open RealSparse (execute execute_sound)
open RealSimulation.Control

/-- Select two adjacent runs, including a short final run, using only
charged natural comparisons, copies, addition, and subtraction. -/
def program : Machine := ⟨[
  .branchIndexLE 18 17 1 3,
  .indexCopy 3 18,.jump 5,.indexCopy 3 17,.jump 5,
  .indexSubtract 12 17 3,
  .branchIndexLE 18 12 7 9,
  .indexCopy 4 18,.jump 11,.indexCopy 4 12,.jump 11,
  .indexAdd 5 3 4,.indexCopy 24 5,.indexAdd 25 24 24,
  .indexCopy 6 19,.indexCopy 7 20,
  .indexAdd 8 19 3,.indexAdd 8 8 3,.indexAdd 9 20 3,
  .indexCopy 10 21,.indexCopy 11 22,.halt]⟩

def leftSize (s : RAMState) : ℕ := min (s.indices 18) (s.indices 17)

def rightSize (s : RAMState) : ℕ := min (s.indices 18) (s.indices 17-leftSize s)

noncomputable def selected (s : RAMState) : RAMState :=
  let l := leftSize s
  let r := rightSize s
  let t := s.setIndex 3 l
  let t := t.setIndex 12 (s.indices 17-l)
  let t := t.setIndex 4 r
  {t with pc := 11}

noncomputable def initialized (s : RAMState) : RAMState :=
  let l := leftSize s
  let r := rightSize s
  let t := selected s
  let t := t.setIndex 5 (l+r)
  let t := t.setIndex 24 (l+r)
  let t := t.setIndex 25 ((l+r)+(l+r))
  let t := t.setIndex 6 (s.indices 19)
  let t := t.setIndex 7 (s.indices 20)
  let t := t.setIndex 8 (s.indices 19+l)
  let t := t.setIndex 8 (s.indices 19+l+l)
  let t := t.setIndex 9 (s.indices 20+l)
  let t := t.setIndex 10 (s.indices 21)
  let t := t.setIndex 11 (s.indices 22)
  {t with pc := 21}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem select_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (program.next input tape) 7 s=some (selected s) := by
  by_cases hl : s.indices 18≤s.indices 17
  · by_cases hr : s.indices 18≤s.indices 17-s.indices 18
    · simp [execute,program,Machine.next,RAMState.setIndex,selected,leftSize,rightSize,
        hp,hl,hr]
    · simp [execute,program,Machine.next,RAMState.setIndex,selected,leftSize,rightSize,
        hp,hl,hr,min_eq_right (le_of_not_ge hr)]
  · have hmin := min_eq_right (le_of_not_ge hl)
    have hn : s.indices 18≠0 := by omega
    simp [execute,program,Machine.next,RAMState.setIndex,selected,leftSize,rightSize,
      hp,hl,hmin,hn]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (program.next input tape) 17 s=some (initialized s) := by
  rw [show 17=7+10 from rfl,RealSparse.execute_add,select_steps input tape s hp]
  simp [execute,program,Machine.next,RAMState.setIndex,initialized,selected]

theorem executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call program) 18 s (Store.ofState (initialized s.val)) := by
  apply Executes.call _ s _ 17 (execute_sound _ (steps input tape s.val s.property))
  rfl

/-- Pass metadata is independent of the merge's temporary count and cursor bank. -/
structure Ready (s : RAMState) (src dst : Buffer) (width remaining : ℕ) : Prop where
  zero : s.indices 0=0
  one : s.indices 1=1
  two : s.indices 2=2
  remaining : s.indices 17=remaining
  width : s.indices 18=width
  sourceRow : s.indices 19=src.coordinates
  sourceValue : s.indices 20=src.coefficients
  targetRow : s.indices 21=dst.coordinates
  targetValue : s.indices 22=dst.coefficients

theorem indices_frame (s : RAMState) (j : ℕ)
    (hj : j<3 ∨(13≤j ∧ j<24) ∨26≤j) : (initialized s).indices j=s.indices j := by
  simp [initialized,selected,RAMState.setIndex,show j≠3 by omega,show j≠4 by omega,
    show j≠5 by omega,show j≠6 by omega,show j≠7 by omega,show j≠8 by omega,
    show j≠9 by omega,show j≠10 by omega,show j≠11 by omega,show j≠12 by omega,
    show j≠24 by omega,show j≠25 by omega]

theorem words_frame (s : RAMState) : (initialized s).words=s.words := rfl

theorem ready_preserved {s : RAMState} {src dst : Buffer} {width remaining : ℕ}
    (h : Ready s src dst width remaining) : Ready (initialized s) src dst width remaining := by
  constructor
  · exact (indices_frame s 0 (by omega)).trans h.zero
  · exact (indices_frame s 1 (by omega)).trans h.one
  · exact (indices_frame s 2 (by omega)).trans h.two
  · exact (indices_frame s 17 (by omega)).trans h.remaining
  · exact (indices_frame s 18 (by omega)).trans h.width
  · exact (indices_frame s 19 (by omega)).trans h.sourceRow
  · exact (indices_frame s 20 (by omega)).trans h.sourceValue
  · exact (indices_frame s 21 (by omega)).trans h.targetRow
  · exact (indices_frame s 22 (by omega)).trans h.targetValue

theorem configuration {s : RAMState} {src dst : Buffer} {width remaining : ℕ}
    (h : Ready s src dst width remaining) :
    Merge.Config (initialized s) src (min width remaining)
      (src.shift (min width remaining)) (min width (remaining-min width remaining)) dst := by
  constructor <;> simp [initialized,selected,RAMState.setIndex,leftSize,rightSize,Buffer.shift,
    h.zero,h.one,h.two,h.remaining,h.width,h.sourceRow,h.sourceValue,h.targetRow,h.targetValue,
    two_mul,Nat.add_assoc]

theorem saved_sizes {s : RAMState} {src dst : Buffer} {width remaining : ℕ}
    (h : Ready s src dst width remaining) :
    (initialized s).indices 24=min width remaining+min width (remaining-min width remaining) ∧
    (initialized s).indices 25=2*(min width remaining+min width (remaining-min width remaining)) := by
  simp [initialized,selected,RAMState.setIndex,leftSize,rightSize,h.remaining,h.width,two_mul]

theorem data_frame (s : RAMState) (out : Buffer) : DataFrame out 0 s (initialized s) := by
  constructor
  · intro j hj _
    exact indices_frame s j (Or.inr (Or.inr (by omega)))
  · intro _ _ _; rfl

end Maxwell.Cost.RealSparseOrder.PassSetup
