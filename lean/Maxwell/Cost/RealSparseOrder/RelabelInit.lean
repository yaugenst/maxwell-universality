import Maxwell.Cost.RealSparseOrder.RelabelState

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSparse (execute execute_sound)
open RealSimulation.Control

/-- The two sorted-record buffers occupy at most four natural cells per
input record. The gathered map/RHS begins immediately beyond that region. -/
def outputBase (m : ℕ) : ℕ := 100+4*m

def initProgram : Machine := ⟨[
  .indexCopy 32 26,.indexCopy 33 27,.indexLiteral 34 0,.indexLiteral 35 0,.indexLiteral 36 0,
  .indexAdd 40 26 26,.indexAdd 40 40 40,.indexLiteral 41 100,
  .indexAdd 40 40 41,.indexCopy 41 40,.halt]⟩

noncomputable def initialized (s : RAMState) : RAMState :=
  let t := s.setIndex 32 (s.indices 26)
  let t := t.setIndex 33 (s.indices 27)
  let t := t.setIndex 34 0
  let t := t.setIndex 35 0
  let t := t.setIndex 36 0
  let t := t.setIndex 40 (s.indices 26+s.indices 26)
  let t := t.setIndex 40 ((s.indices 26+s.indices 26)+(s.indices 26+s.indices 26))
  let t := t.setIndex 41 100
  let t := t.setIndex 40 (outputBase (s.indices 26))
  t.setIndex 41 (outputBase (s.indices 26))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem init_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (initProgram.next input tape) 10 s=some (initialized s) := by
  have he : s.indices 26+s.indices 26+(s.indices 26+s.indices 26)+100=outputBase (s.indices 26) := by
    unfold outputBase; omega
  simp (config:={maxSteps:=250000}) [execute,initProgram,Machine.next,initialized,RAMState.setIndex,hp,he]

theorem init_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call initProgram) 11 s (Store.ofState (initialized s.val)) := by
  apply Executes.call _ s _ 10 (execute_sound _ (init_steps input tape s.val s.property))
  simp [initProgram,initialized,RAMState.setIndex,s.property]

theorem init_config (s : RAMState) (b : Buffer) (m : ℕ)
    (h0 : s.indices 0=0) (h1 : s.indices 1=1) (h2 : s.indices 2=2)
    (hm : s.indices 26=m) (hb : s.indices 27=b.coordinates) :
    Config (initialized s) b m none 0 m (outputBase m) (outputBase m) := by
  constructor <;> simp [initialized,RAMState.setIndex,h0,h1,h2,hm,hb]

theorem initialized_indices_frame (s : RAMState) (j : ℕ) (hj : j<32 ∨42≤j) :
    (initialized s).indices j=s.indices j := by
  simp [initialized,RAMState.setIndex,show j≠32 by omega,show j≠33 by omega,
    show j≠34 by omega,show j≠35 by omega,show j≠36 by omega,
    show j≠40 by omega,show j≠41 by omega]

theorem initialized_words_frame (s : RAMState) : (initialized s).words=s.words := rfl

theorem initialized_records {s : RAMState} {b : Buffer} {es : List SparseEntry}
    (h : Records b s es) (hb : b.Safe) : Records b (initialized s) es := by
  induction es generalizing b with
  | nil => trivial
  | cons e es ih =>
    exact ⟨(initialized_indices_frame s b.coordinates (Or.inr (by have hh:=hb.2; omega))).trans h.1,
      (initialized_indices_frame s (b.coordinates+1) (Or.inr (by have hh:=hb.2; omega))).trans h.2.1,
      h.2.2.1,ih h.2.2.2 (hb.shift 1)⟩

end Maxwell.Cost.RealSparseOrder.Relabel
