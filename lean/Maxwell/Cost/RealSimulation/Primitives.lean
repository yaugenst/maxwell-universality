import Maxwell.Cost.RealSimulation.ControlCorrectness

namespace Maxwell.Cost.RealSimulation.Control

def Store.put (s : Store) (register value : ℕ) : Store :=
  ⟨{s.val with indices := Function.update s.val.indices register value, pc := 0}, rfl⟩

@[simp] theorem Store.put_indices (s : Store) (r v j : ℕ) :
    (s.put r v).val.indices j = if j = r then v else s.val.indices j := by
  simp [put, Function.update_apply]

@[simp] theorem Store.put_put (s : Store) (r a b : ℕ) :
    (s.put r a).put r b = s.put r b := by
  apply Subtype.ext
  simp [put, Function.update_idem]

def literal (dst value : ℕ) : Code := .call ⟨[.indexLiteral dst value, .halt]⟩
def copy (dst src : ℕ) : Code := .call ⟨[.indexCopy dst src, .halt]⟩
def add (dst left right : ℕ) : Code := .call ⟨[.indexAdd dst left right, .halt]⟩
def subtract (dst left right : ℕ) : Code :=
  .call ⟨[.indexSubtract dst left right, .halt]⟩
def load (dst address : ℕ) : Code := .call ⟨[.loadIndex dst address, .halt]⟩
def save (address src : ℕ) : Code := .call ⟨[.storeIndex address src, .halt]⟩

theorem literal_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst value : ℕ) : Executes input tape (literal dst value) 2 s (s.put dst value) := by
  apply Executes.call (t := s.val.setIndex dst value) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

theorem copy_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst src : ℕ) : Executes input tape (copy dst src) 2 s
      (s.put dst (s.val.indices src)) := by
  apply Executes.call (t := s.val.setIndex dst (s.val.indices src)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

theorem add_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst left right : ℕ) : Executes input tape (add dst left right) 2 s
      (s.put dst (s.val.indices left + s.val.indices right)) := by
  apply Executes.call
    (t := s.val.setIndex dst (s.val.indices left + s.val.indices right)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

theorem subtract_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst left right : ℕ) : Executes input tape (subtract dst left right) 2 s
      (s.put dst (s.val.indices left - s.val.indices right)) := by
  apply Executes.call
    (t := s.val.setIndex dst (s.val.indices left - s.val.indices right)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

theorem load_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst address : ℕ) : Executes input tape (load dst address) 2 s
      (s.put dst (s.val.indices (s.val.indices address))) := by
  apply Executes.call
    (t := s.val.setIndex dst (s.val.indices (s.val.indices address))) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

theorem save_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address src : ℕ) : Executes input tape (save address src) 2 s
      (s.put (s.val.indices address) (s.val.indices src)) := by
  apply Executes.call
    (t := s.val.setIndex (s.val.indices address) (s.val.indices src)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setIndex, s.property]

/-- Multiplication by a fixed bank stride is a finite list of additions.
Its size and runtime depend on the fixed source program, not the input. -/
def repeatAdd (dst src : ℕ) : ℕ → Code
  | 0 => .skip
  | n + 1 => .seq (add dst dst src) (repeatAdd dst src n)

theorem repeatAdd_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst src n : ℕ) (hne : src ≠ dst) :
    Executes input tape (repeatAdd dst src n) (2 * n + 1) s
      (s.put dst (s.val.indices dst + n * s.val.indices src)) := by
  induction n generalizing s with
  | zero =>
    have he : s.put dst (s.val.indices dst) = s := by
      apply Subtype.ext
      simp [Store.put, Function.update_eq_self, ← s.property]
    simpa [repeatAdd, he] using Executes.skip (input := input) (randomTape := tape) s
  | succ n ih =>
    have h := (add_executes input tape s dst dst src).seq
      (ih (s.put dst (s.val.indices dst + s.val.indices src)))
    simpa [repeatAdd, hne, Nat.mul_add, Nat.add_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h

end Maxwell.Cost.RealSimulation.Control
