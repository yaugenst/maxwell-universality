import Maxwell.Continuum.RationalDataflowMeaning

/-! Bounded finite loops preserve shared values and pay for each actual arithmetic stage. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

def loopInstructions (body : ℕ→List Instruction) (n : ℕ) : List Instruction :=
  (List.range n).flatMap body

def loopState (body : ℕ→List Instruction) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | n+1 => evaluate (body n) (loopState body v n)

theorem loopInstructions_succ (body : ℕ→List Instruction) (n : ℕ) :
    loopInstructions body (n+1)=loopInstructions body n++body n := by
  simp [loopInstructions,List.range_succ,List.flatMap_append]

theorem evaluate_loop (body : ℕ→List Instruction) (n : ℕ) (v : ℕ→Parts) :
    evaluate (loopInstructions body n) v=loopState body v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loopInstructions_succ,evaluate_append,ih]; rfl

theorem loop_valid (S : Finset ℕ) (body : ℕ→List Instruction) (n : ℕ)
    (hv : ∀ k<n, ∀ a∈body k, a.Valid S) :
    ∀ a∈loopInstructions body n, a.Valid S := by
  intro a ha
  obtain ⟨k,hk,ha⟩ := List.mem_flatMap.mp ha
  exact hv k (List.mem_range.mp hk) a ha

theorem loop_length_le (body : ℕ→List Instruction) (n D : ℕ)
    (hD : ∀ k<n, (body k).length≤D) : (loopInstructions body n).length≤n*D := by
  induction n with
  | zero => simp [loopInstructions]
  | succ n ih =>
    rw [loopInstructions_succ,List.length_append,Nat.succ_mul]
    exact Nat.add_le_add (ih (fun k hk => hD k (by omega))) (hD n (by omega))

theorem loop_widthTrace (S : Finset ℕ) (B : ℕ) (body : ℕ→List Instruction) (n : ℕ)
    (v : ℕ→Parts) (h0 : WidthBank S B v)
    (hw : ∀ k<n, WidthTrace S B (body k) (loopState body v k)) :
    WidthTrace S B (loopInstructions body n) v := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [loopInstructions_succ,widthTrace_append,evaluate_loop]
    exact ⟨ih (fun k hk => hw k (by omega)),hw n (by omega)⟩

theorem admissibleTrace_append (xs ys : List Instruction) (v : ℕ→Parts) :
    AdmissibleTrace (xs++ys) v ↔ AdmissibleTrace xs v ∧ AdmissibleTrace ys (evaluate xs v) := by
  induction xs generalizing v with
  | nil => simp [AdmissibleTrace,evaluate]
  | cons a rest ih =>
    simp only [List.cons_append,AdmissibleTrace,evaluate,ih]
    tauto

theorem loop_admissibleTrace (body : ℕ→List Instruction) (n : ℕ) (v : ℕ→Parts)
    (ha : ∀ k<n, AdmissibleTrace (body k) (loopState body v k)) :
    AdmissibleTrace (loopInstructions body n) v := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [loopInstructions_succ,admissibleTrace_append,evaluate_loop]
    exact ⟨ih (fun k hk => ha k (by omega)),ha n (by omega)⟩

theorem loop_computes (S : Finset ℕ) (body : ℕ→List Instruction) (n D B : ℕ)
    (hv : ∀ k<n, ∀ a∈body k, a.Valid S) (hD : ∀ k<n, (body k).length≤D)
    (v : ℕ→Parts) (h0 : WidthBank S B v)
    (hw : ∀ k<n, WidthTrace S B (body k) (loopState body v k))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t,
      (runPriced ((program (loopInstructions body n)).compile.next input tape)
        (n*D*operationCost B+2) s.val).finished=some (t.place (program (loopInstructions body n)).size) ∧
      (runPriced ((program (loopInstructions body n)).compile.next input tape)
        (n*D*operationCost B+2) s.val).instructions=cost ∧
      cost≤n*D*operationCost B+1 ∧ Ready S (loopState body v n) t := by
  obtain ⟨cost,t,he,hc,hb,_⟩ := program_executes S (loopInstructions body n) (loop_valid S body n hv)
    v B (loop_widthTrace S B body n v h0 hw) input tape s hs
  have hlen := Nat.mul_le_mul_right (operationCost B) (loop_length_le body n D hD)
  have hbound : cost≤n*D*operationCost B+1 := by omega
  obtain ⟨hrun,hcost⟩ := he.compiled_run (n*D*operationCost B+2) (by omega)
  rw [evaluate_loop] at hb
  exact ⟨cost,t,hrun,hcost,hbound,hb⟩

#print axioms loop_computes

end Maxwell.Continuum.RationalDataflow
