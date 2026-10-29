import Maxwell.Cost.RealSparseOrder.Emit
import Maxwell.Cost.RealSparseOrder.Order

namespace Maxwell.Cost.RealSparseOrder.Compare
open RealSparse (execute execute_sound)
open RealSimulation.Control

/-- Load both actual coordinate pairs, without comparing coefficients. -/
def program : Machine := ⟨[
  .loadIndex 13 6,.indexAdd 12 6 1,.loadIndex 14 12,
  .loadIndex 15 8,.indexAdd 12 8 1,.loadIndex 16 12,.halt]⟩

noncomputable def loaded (s : RAMState) : RAMState :=
  let t := s.setIndex 13 (s.indices (s.indices 6))
  let t := t.setIndex 12 (s.indices 6+1)
  let t := t.setIndex 14 (s.indices (s.indices 6+1))
  let t := t.setIndex 15 (s.indices (s.indices 8))
  let t := t.setIndex 12 (s.indices 8+1)
  t.setIndex 16 (s.indices (s.indices 8+1))

def Ready (s : RAMState) : Prop :=
  s.pc=0 ∧ s.indices 1=1 ∧ 100≤s.indices 6 ∧ 100≤s.indices 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hr : Ready s) :
    execute (program.next input tape) 6 s=some (loaded s) := by
  rcases hr with ⟨hpc,h1,hl,hr⟩
  have hleft : ∀j:ℕ,j<17→s.indices 6≠j := by omega
  have hleftNext : ∀j:ℕ,j<17→s.indices 6+1≠j := by omega
  have hright : ∀j:ℕ,j<17→s.indices 8≠j := by omega
  have hrightNext : ∀j:ℕ,j<17→s.indices 8+1≠j := by omega
  simp [execute,program,Machine.next,RAMState.setIndex,loaded,hpc,h1,
    hleftNext,hright,hrightNext]

theorem executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) (hr : Ready s.val) :
    Executes input tape (.call program) 7 s (Store.ofState (loaded s.val)) := by
  apply Executes.call _ s _ 6 (execute_sound _ (steps input tape s.val hr))
  simp [program,loaded,RAMState.setIndex,hr.1]

theorem registers (s : RAMState) :
    (loaded s).indices 13=s.indices (s.indices 6) ∧
    (loaded s).indices 14=s.indices (s.indices 6+1) ∧
    (loaded s).indices 15=s.indices (s.indices 8) ∧
    (loaded s).indices 16=s.indices (s.indices 8+1) := by
  simp [loaded,RAMState.setIndex]

theorem indices_frame (s : RAMState) (j : ℕ) (hj : j<12 ∨17≤j) :
    (loaded s).indices j=s.indices j := by
  simp [loaded,RAMState.setIndex,show j≠12 by omega,show j≠13 by omega,
    show j≠14 by omega,show j≠15 by omega,show j≠16 by omega]

/-- Three natural comparisons implement lexicographic order, including ties. -/
def choose (yes no : Code) : Code :=
  .branch 13 15 (.branch 15 13 (.branch 14 16 yes no) yes) no

theorem choose_left (input : RAMInput) (tape : ℕ→Bool)
    (yes no : Code) (s t : Store) (cost : ℕ)
    (h : s.val.indices 13<s.val.indices 15 ∨
      (s.val.indices 13=s.val.indices 15 ∧ s.val.indices 14≤s.val.indices 16))
    (run : Executes input tape yes cost s t) :
    ∃total, total≤cost+3 ∧ Executes input tape (choose yes no) total s t := by
  rcases h with h|⟨he,hc⟩
  · exact ⟨1+(1+cost),by omega,.yes (by omega) (.no (by omega) run)⟩
  · exact ⟨1+(1+(1+cost)),by omega,.yes (by omega) (.yes (by omega) (.yes hc run))⟩

theorem choose_right (input : RAMInput) (tape : ℕ→Bool)
    (yes no : Code) (s t : Store) (cost : ℕ)
    (h : ¬(s.val.indices 13<s.val.indices 15 ∨
      (s.val.indices 13=s.val.indices 15 ∧ s.val.indices 14≤s.val.indices 16)))
    (run : Executes input tape no cost s t) :
    ∃total, total≤cost+3 ∧ Executes input tape (choose yes no) total s t := by
  by_cases he : s.val.indices 13≤s.val.indices 15
  · have heq : s.val.indices 13=s.val.indices 15 := by omega
    exact ⟨1+(1+(1+cost)),by omega,.yes he (.yes (by omega) (.no (by omega) run))⟩
  · exact ⟨1+cost,by omega,.no he run⟩

end Maxwell.Cost.RealSparseOrder.Compare
