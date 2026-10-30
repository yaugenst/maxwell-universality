import Maxwell.Continuum.RationalExpression

/-! A finite expression compiler with fresh shared-register slots. -/

namespace Maxwell.Continuum.Calibration.RationalExpression

open RationalDataflow

def slots : RationalExpression → ℕ
  | .input _ => 0
  | .zero => 1
  | .binary _ a b => a.slots+b.slots+1
  | .inverse a => a.slots+1

def output : RationalExpression → ℕ → ℕ
  | .input i,_ => i
  | .zero,s => s
  | .binary _ a b,s => s+a.slots+b.slots
  | .inverse a,s => s+a.slots

def instructions : RationalExpression → ℕ → List Instruction
  | .input _,_ => []
  | .zero,s => [.literal s 0]
  | .binary op a b,s => a.instructions s++b.instructions (s+a.slots)++
      [.binary op (s+a.slots+b.slots) (a.output s) (b.output (s+a.slots))]
  | .inverse a,s => a.instructions s++[.inverse (s+a.slots) (a.output s)]

theorem instructions_length (e : RationalExpression) (s : ℕ) : (e.instructions s).length=e.slots := by
  induction e generalizing s with
  | input i => rfl
  | zero => rfl
  | binary op a b ia ib => simp only [instructions,List.length_append,List.length_singleton,ia,ib,slots]
  | inverse a ih => simp only [instructions,List.length_append,List.length_singleton,ih,slots]

theorem slots_le_nodes (e : RationalExpression) : e.slots≤e.nodes := by
  induction e with
  | input i => simp only [slots,nodes]; omega
  | zero => decide
  | binary op a b ia ib => simp only [slots,nodes]; omega
  | inverse a ih => simp only [slots,nodes]; omega

theorem output_lt (e : RationalExpression) (s : ℕ) (he : e.Below s) : e.output s<s+e.slots := by
  cases e with
  | input i => exact he
  | zero => simp only [output,slots]; omega
  | binary op a b => simp only [output,slots]; omega
  | inverse a => simp only [output,slots]; omega

def writeIndex : Instruction → ℕ
  | .literal t _ => t
  | .binary _ t _ _ => t
  | .inverse t _ => t

theorem instruction_update_of_ne (a : Instruction) (v : ℕ → Parts) (i : ℕ) (hi : i≠writeIndex a) :
    a.update v i=v i := by
  cases a <;> exact Function.update_of_ne hi _ _

theorem evaluate_preserves (ins : List Instruction) (v : ℕ → Parts) (i : ℕ)
    (hi : ∀ a∈ins, i≠writeIndex a) : RationalDataflow.evaluate ins v i=v i := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih =>
    rw [RationalDataflow.evaluate,ih (a.update v) (fun b hb => hi b (by simp [hb]))]
    exact instruction_update_of_ne a v i (hi a (by simp))

theorem instruction_write_range (e : RationalExpression) (s : ℕ) (a : Instruction)
    (ha : a∈e.instructions s) : s≤writeIndex a ∧ writeIndex a<s+e.slots := by
  induction e generalizing s with
  | input i => simp only [instructions,List.not_mem_nil] at ha
  | zero =>
    simp only [instructions,List.mem_singleton] at ha
    subst a
    simp only [writeIndex,slots]
    omega
  | binary op l r il ir =>
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (hl|hr)|rfl
    · have h := il s hl
      simp only [slots]
      omega
    · have h := ir (s+l.slots) hr
      simp only [slots]
      omega
    · simp only [writeIndex,slots]
      omega
  | inverse e ih =>
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · have h := ih s ha
      simp only [slots]
      omega
    · simp only [writeIndex,slots]
      omega

theorem instructions_frame (e : RationalExpression) (s : ℕ) (v : ℕ → Parts) (i : ℕ)
    (hi : i<s ∨ s+e.slots ≤ i) : RationalDataflow.evaluate (e.instructions s) v i=v i := by
  apply evaluate_preserves
  intro a ha
  have h := instruction_write_range e s a ha
  omega

theorem instructions_valid (e : RationalExpression) (s M : ℕ) (he : e.Below s) (hM : s+e.slots≤M) :
    ∀ a∈e.instructions s, a.Valid (Finset.range M) := by
  induction e generalizing s with
  | input i => intro a ha; simp only [instructions,List.not_mem_nil] at ha
  | zero =>
    intro a ha
    simp only [instructions,List.mem_singleton] at ha
    subst a
    change s∈Finset.range M
    simp only [Finset.mem_range]
    change s+1≤M at hM
    omega
  | binary op l r il ir =>
    intro a ha
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (hl|hr)|rfl
    · exact il s he.1 (by simp only [slots] at hM; omega) a hl
    · exact ir (s+l.slots) (he.2.mono (by omega)) (by simp only [slots] at hM; omega) a hr
    · have hl := output_lt l s he.1
      have hr := output_lt r (s+l.slots) (he.2.mono (by omega))
      simp only [Instruction.Valid,Finset.mem_range]
      simp only [slots] at hM
      omega
  | inverse e ih =>
    intro a ha
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · exact ih s he (by simp only [slots] at hM; omega) a ha
    · have ho := output_lt e s he
      simp only [Instruction.Valid,Finset.mem_range]
      simp only [slots] at hM
      omega

#print axioms instructions_frame
#print axioms instructions_valid

end Maxwell.Continuum.Calibration.RationalExpression
