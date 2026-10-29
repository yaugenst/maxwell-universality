import Maxwell.Cost.RealPrivate.Compiler

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem realLiteral_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst : ℕ) (q : ℚ) : Executes input tape (realLiteral dst q) 2 s (putWord s dst q) := by
  apply Executes.call (t := s.val.setWord dst q) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realLoad_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst address : ℕ) : Executes input tape (realLoad dst address) 2 s
      (putWord s dst (s.val.words (s.val.indices address))) := by
  apply Executes.call (t := s.val.setWord dst (s.val.words (s.val.indices address))) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realStore_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address src : ℕ) : Executes input tape (realStore address src) 2 s
      (putWord s (s.val.indices address) (s.val.words src)) := by
  apply Executes.call (t := s.val.setWord (s.val.indices address) (s.val.words src)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realAdd_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst left right : ℕ) : Executes input tape (realAdd dst left right) 2 s
      (putWord s dst (s.val.words left + s.val.words right)) := by
  apply Executes.call (t := s.val.setWord dst (s.val.words left + s.val.words right)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realMultiply_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst left right : ℕ) : Executes input tape (realMultiply dst left right) 2 s
      (putWord s dst (s.val.words left * s.val.words right)) := by
  apply Executes.call (t := s.val.setWord dst (s.val.words left * s.val.words right)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realDivide_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (dst left right : ℕ) : Executes input tape (realDivide dst left right) 2 s
      (putWord s dst (s.val.words left / s.val.words right)) := by
  apply Executes.call (t := s.val.setWord dst (s.val.words left / s.val.words right)) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

noncomputable def drawn (s : Store) (dst : ℕ) (b : Bool) : Store :=
  ⟨{(putWord s dst (if b then 1 else 0)).val with randomCursor := s.val.randomCursor + 1}, rfl⟩

theorem randomBit_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) (dst : ℕ) :
    Executes input tape (randomBit dst) 2 s (drawn s dst (tape s.val.randomCursor)) := by
  apply Executes.call (t := {(s.val.setWord dst (if tape s.val.randomCursor then 1 else 0)) with
    randomCursor := s.val.randomCursor + 1}) (cost := 1)
  · exact Steps.step (by simp [Machine.next, s.property]) (Steps.refl _)
  · simp [RAMState.setWord, s.property]

theorem realBranch_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) (yes no : ℕ) :
    Executes input tape (realBranch yes no) 4 s
      (s.put sourcePC (if s.val.words 0 ≤ s.val.words 1 then yes else no)) := by
  classical
  by_cases hc : s.val.words 0 ≤ s.val.words 1
  · simp only [ite_eq_left hc]
    apply Executes.call (t := {s.val with
      pc := 5
      indices := Function.update s.val.indices sourcePC yes}) (cost := 3)
    · apply advance_steps
      simp [advance, Machine.next, s.property, hc, RAMState.setIndex]
    · rfl
  · simp only [ite_eq_right hc]
    apply Executes.call (t := {s.val with
      pc := 5
      indices := Function.update s.val.indices sourcePC no}) (cost := 3)
    · apply advance_steps
      simp [advance, Machine.next, s.property, hc, RAMState.setIndex]
    · rfl

theorem staticPointer_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (bank address : ℕ) : Executes input tape (staticPointer bank address) 4 s
      (s.put pointerRegister (slot (s.val.indices originRegister) bank address)) := by
  have h := (literal_executes input tape s pointerRegister (4 * address + bank)).seq
    (add_executes input tape (s.put pointerRegister (4 * address + bank))
      pointerRegister pointerRegister originRegister)
  simpa [staticPointer, slot, pointerRegister, originRegister, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem bankPointer_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (bank coordinate : ℕ) (hne : coordinate ≠ pointerRegister) :
    Executes input tape (bankPointer bank coordinate) 13 s
      (s.put pointerRegister (slot (s.val.indices originRegister) bank (s.val.indices coordinate))) := by
  let s0 := s.put pointerRegister bank
  let s1 := s0.put pointerRegister (s0.val.indices pointerRegister + s0.val.indices originRegister)
  have h := (literal_executes input tape s pointerRegister bank).seq
    ((add_executes input tape s0 pointerRegister pointerRegister originRegister).seq
      (repeatAdd_executes input tape s1 pointerRegister coordinate 4 hne))
  have hn : coordinate ≠ 0 := hne
  simpa [bankPointer, block, RealSimulation.sequence, s0, s1, slot, pointerRegister,
    originRegister, hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem inputPointer_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (base stride coordinate : ℕ) (hne : coordinate ≠ pointerRegister) :
    Executes input tape (inputPointer base stride coordinate) (2 * stride + 3) s
      (s.put pointerRegister (s.val.indices base + stride * s.val.indices coordinate)) := by
  have h := (copy_executes input tape s pointerRegister base).seq
    (repeatAdd_executes input tape (s.put pointerRegister (s.val.indices base))
      pointerRegister coordinate stride hne)
  convert h using 1 <;> first | omega | simp [inputPointer, hne]

end Maxwell.Cost.RealPrivate
