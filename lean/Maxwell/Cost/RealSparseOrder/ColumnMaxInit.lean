import Maxwell.Cost.RealSparseOrder.ColumnMaxState

namespace Maxwell.Cost.RealSparseOrder.ColumnMax
open RealSparse (execute execute_sound)
open RealSimulation.Control RealSimulation.IndexWidth

def initProgram : Machine := ⟨[
  .indexLiteral 42 0,.indexCopy 43 26,.indexAdd 44 27 1,.halt]⟩

noncomputable def initialized (s : RAMState) : RAMState :=
  ((s.setIndex 42 0).setIndex 43 (s.indices 26)).setIndex 44 (s.indices 27+1)

theorem init_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (h1 : s.val.indices 1=1) :
    Executes input tape (.call initProgram) 4 s (Store.ofState (initialized s.val)) := by
  apply Executes.call _ s _ 3
  · apply execute_sound
    simp [execute,initProgram,Machine.next,initialized,RAMState.setIndex,s.property,h1]
  · simp [initProgram,initialized,RAMState.setIndex,s.property]

theorem init_config (s : RAMState) (b : Buffer) (n : ℕ)
    (h1 : s.indices 1=1) (h2 : s.indices 2=2)
    (hn : s.indices 26=n) (hc : s.indices 27=b.coordinates) :
    Config (initialized s) b n 0 := by
  constructor <;> simp [initialized,RAMState.setIndex,h1,h2,hn,hc]

theorem initialized_frame (s : RAMState) (j : ℕ) (hj : j<42 ∨45≤j) :
    (initialized s).indices j=s.indices j := by
  simp [initialized,RAMState.setIndex,show j≠42 by omega,show j≠43 by omega,show j≠44 by omega]

theorem initialized_index_bound {B : ℕ} {s : RAMState} (hs : IndexBound B s)
    (hc : s.indices 27+1≤B) : IndexBound B (initialized s) :=
  ((hs.setIndex 42 0 (Nat.zero_le _)).setIndex 43 _ (hs 26)).setIndex 44 _ hc

theorem initialized_records {s : RAMState} {b : Buffer} {es : List SparseEntry}
    (h : Records b s es) (hb : b.Safe) : Records b (initialized s) es := by
  induction es generalizing b with
  | nil => trivial
  | cons e es ih =>
    exact ⟨(initialized_frame s b.coordinates (Or.inr (by have hh:=hb.2; omega))).trans h.1,
      (initialized_frame s (b.coordinates+1) (Or.inr (by have hh:=hb.2; omega))).trans h.2.1,
      h.2.2.1,ih h.2.2.2 (hb.shift 1)⟩

end Maxwell.Cost.RealSparseOrder.ColumnMax
