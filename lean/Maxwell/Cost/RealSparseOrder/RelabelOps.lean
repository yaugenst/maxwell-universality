import Maxwell.Cost.RealSparseOrder.RelabelPure
import Maxwell.Cost.RealSparseOrder.Memory

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSparse (execute execute_sound)
open RealSimulation.Control

def loadProgram : Machine := ⟨[.loadIndex 37 33,.halt]⟩

noncomputable def loaded (s : RAMState) : RAMState :=
  s.setIndex 37 (s.indices (s.indices 33))

theorem load_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call loadProgram) 2 s (Store.ofState (loaded s.val)) := by
  apply Executes.call _ s _ 1
  · apply execute_sound
    simp [execute,loadProgram,Machine.next,loaded,s.property]
  · simp [loadProgram,loaded,RAMState.setIndex,s.property]

/-- Store a newly encountered original label and read its right-hand side
from the input tape at the actual address `entryCount + originalRow`. -/
def createProgram : Machine := ⟨[
  .indexAdd 38 40 35,.storeIndex 38 37,.indexAdd 39 26 37,.input 0 39,
  .indexAdd 38 41 35,.store 38 0,.indexCopy 34 37,.indexAdd 35 35 1,
  .indexLiteral 36 1,.halt]⟩

noncomputable def created (input : RAMInput) (s : RAMState) : RAMState :=
  let t := s.setIndex 38 (s.indices 40+s.indices 35)
  let t := t.setIndex (s.indices 40+s.indices 35) (s.indices 37)
  let t := t.setIndex 39 (s.indices 26+s.indices 37)
  let t := t.setWord 0 (input.words (s.indices 26+s.indices 37))
  let t := t.setIndex 38 (s.indices 41+s.indices 35)
  let t := t.setWord (s.indices 41+s.indices 35) (input.words (s.indices 26+s.indices 37))
  let t := t.setIndex 34 (s.indices 37)
  let t := t.setIndex 35 (s.indices 35+1)
  t.setIndex 36 1

def CreateReady (s : RAMState) : Prop :=
  s.pc=0 ∧s.indices 1=1 ∧100≤s.indices 40 ∧100≤s.indices 41

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1200000 in
theorem create_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (h : CreateReady s) :
    execute (createProgram.next input tape) 9 s=some (created input s) := by
  rcases h with ⟨hp,h1,hm,hr⟩
  have hi : ∀j:ℕ,j<42→j≠s.indices 40+s.indices 35 := by omega
  simp (config:={maxSteps:=250000}) [execute,createProgram,Machine.next,created,
    RAMState.setIndex,RAMState.setWord,hp,h1,hi]

theorem create_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) (h : CreateReady s.val) :
    Executes input tape (.call createProgram) 10 s (Store.ofState (created input s.val)) := by
  apply Executes.call _ s _ 9 (execute_sound _ (create_steps input tape s.val h))
  simp [createProgram,created,RAMState.setIndex,RAMState.setWord,s.property]

def rewriteProgram : Machine := ⟨[
  .indexSubtract 37 35 1,.storeIndex 33 37,.indexAdd 33 33 2,
  .indexSubtract 32 32 1,.halt]⟩

noncomputable def rewritten (s : RAMState) : RAMState :=
  let t := s.setIndex 37 (s.indices 35-1)
  let t := t.setIndex (s.indices 33) (s.indices 35-1)
  let t := t.setIndex 33 (s.indices 33+2)
  t.setIndex 32 (s.indices 32-1)

def RewriteReady (s : RAMState) : Prop :=
  s.pc=0 ∧s.indices 1=1 ∧s.indices 2=2 ∧100≤s.indices 33

theorem rewrite_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (h : RewriteReady s) :
    execute (rewriteProgram.next input tape) 4 s=some (rewritten s) := by
  rcases h with ⟨hp,h1,h2,hr⟩
  have hi : ∀j:ℕ,j<42→j≠s.indices 33 := by omega
  simp [execute,rewriteProgram,Machine.next,rewritten,RAMState.setIndex,hp,h1,h2,hi]

theorem rewrite_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) (h : RewriteReady s.val) :
    Executes input tape (.call rewriteProgram) 5 s (Store.ofState (rewritten s.val)) := by
  apply Executes.call _ s _ 4 (execute_sound _ (rewrite_steps input tape s.val h))
  simp [rewriteProgram,rewritten,RAMState.setIndex,s.property]

theorem loaded_indices_frame (s : RAMState) (j : ℕ) (h : j≠37) :
    (loaded s).indices j=s.indices j := by simp [loaded,RAMState.setIndex,h]

theorem created_indices_frame (input : RAMInput) (s : RAMState) (j : ℕ)
    (hj : j<34 ∨j=37 ∨40≤j) (hm : j≠s.indices 40+s.indices 35) :
    (created input s).indices j=s.indices j := by
  simp [created,RAMState.setIndex,RAMState.setWord,hm,show j≠34 by omega,
    show j≠35 by omega,show j≠36 by omega,show j≠38 by omega,show j≠39 by omega]

theorem created_words_frame (input : RAMInput) (s : RAMState) (j : ℕ)
    (h0 : j≠0) (hr : j≠s.indices 41+s.indices 35) :
    (created input s).words j=s.words j := by
  simp [created,RAMState.setIndex,RAMState.setWord,h0,hr]

theorem rewritten_indices_frame (s : RAMState) (j : ℕ)
    (hj : j<32 ∨(34≤j ∧j<37) ∨38≤j) (hr : j≠s.indices 33) :
    (rewritten s).indices j=s.indices j := by
  simp [rewritten,RAMState.setIndex,hr,show j≠32 by omega,show j≠33 by omega,
    show j≠37 by omega]

theorem rewritten_words_frame (s : RAMState) : (rewritten s).words=s.words := rfl

end Maxwell.Cost.RealSparseOrder.Relabel
