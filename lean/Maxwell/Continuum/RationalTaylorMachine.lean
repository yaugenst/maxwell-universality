import Maxwell.Continuum.RationalTaylorData

/-! A stored-word machine for common-denominator Taylor evaluation. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000

/-- Input words are 600,601; signed output numerator parts and denominator
are 602,603,604. Word605 is the current power and606 a cleared temporary. -/
def ids : Finset ℕ := {600,601,602,603,604,605,606}
def workspace : Finset ℕ := {0,1,2,3,602,603,604,605,606}

def values (a b : ℕ) (signs : ℕ → Sign) (n i : ℕ) : ℕ :=
  if i=600 then a else if i=601 then b else
  if i=602 then numerator a b (fun k => (signs k).positive) n else
  if i=603 then numerator a b (fun k => (signs k).negative) n else
  if i=604 then denominator b n else if i=605 then a^n else 0

def initialization (s : Sign) : List NatAssign.Instruction :=
  [.literal 602 (if s.positive then 1 else 0),
   .literal 603 (if s.negative then 1 else 0),
   .literal 604 1,.literal 605 1,.literal 606 0]

def addTerm : Sign → List NatAssign.Instruction
  | .zero => []
  | .plus => [.add 605 602]
  | .minus => [.add 605 603]

def step (s : Sign) (n : ℕ) : List NatAssign.Instruction :=
  [.literal 606 (n+1),.multiply 601 606,.multiply 606 602,
   .multiply 606 603,.multiply 606 604,.multiply 600 605]++addTerm s++[.literal 606 0]

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem initialization_valid (s : Sign) : ∀ a ∈ initialization s, a.Valid ids := by
  cases s <;> simp [initialization,NatAssign.Instruction.Valid,ids]

theorem step_valid (s : Sign) (n : ℕ) : ∀ a ∈ step s n, a.Valid ids := by
  cases s <;> simp [step,addTerm,NatAssign.Instruction.Valid,ids]

theorem initialization_values (v : ℕ → ℕ) (signs : ℕ → Sign) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values (initialization (signs 0)) v i = values (v 600) (v 601) signs 0 i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [initialization,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,denominator]

theorem step_values (a b : ℕ) (signs : ℕ → Sign) (n : ℕ) :
    NatAssign.values (step (signs (n+1)) n) (values a b signs n) = values a b signs (n+1) := by
  ext i
  by_cases h2 : i=602
  · subst i
    cases h : signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,h,
      Sign.positive,Sign.negative,pow_succ,Nat.mul_comm,Nat.add_comm]
  by_cases h3 : i=603
  · subst i
    cases h : signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,h,
      Sign.positive,Sign.negative,pow_succ,Nat.mul_comm,Nat.add_comm]
  by_cases h4 : i=604
  · subst i
    cases signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,denominator_succ]
  by_cases h5 : i=605
  · subst i
    cases signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h6 : i=606
  · subst i
    cases signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values]
  cases signs (n+1) <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,h2,h3,h4,h5,h6]

theorem values_width (a b : ℕ) (signs : ℕ → Sign) (n N W : ℕ) (hn : n ≤ N)
    (ha : a.bits.length ≤ W) (hb : b.bits.length ≤ W) (i : ℕ) :
    (values a b signs n i).bits.length ≤ width N W := by
  have hW : W ≤ width N W := by unfold width; nlinarith
  have hnum (keep : ℕ → Bool) : (numerator a b keep n).bits.length ≤ width N W :=
    (numerator_bits a b keep N W ha hb n hn).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hd := denominator_bits b n N W hn hb
  have hp := (SelectedParameters.Geometric.power_bits a n).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hn ha) 1)
  have hp' : (a^n).bits.length ≤ width N W := by unfold width; nlinarith only [hp]
  simp only [values]
  split_ifs <;> first | exact ha.trans hW | exact hb.trans hW | exact hnum _ | exact hd | exact hp' | simp

structure Ready (a b : ℕ) (signs : ℕ → Sign) (n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b signs n) s.val
  scratch : NatAssign.Scratch s.val

theorem step_executes (a b : ℕ) (signs : ℕ → Sign) (n N W : ℕ) (hn : n < N)
    (ha : a.bits.length ≤ W) (hb : b.bits.length ≤ W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready a b signs n s) :
    ∃ cost t, Executes input tape (NatAssign.code (step (signs (n+1)) n)) cost s t ∧
      cost ≤ (2 : ℕ)^40*(width N W+2)^2 ∧ Ready a b signs (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,t,he,hc,hbank,hsc,hf⟩ := NatAssign.executes ids ids_ge (step (signs (n+1)) n)
    (step_valid _ _) (values a b signs n) input tape s hs.bank hs.scratch
  have hbound := NatAssign.price_bound ids (step (signs (n+1)) n) (step_valid _ _)
    (values a b signs n) (width N W) (fun i _ => values_width a b signs n N W hn.le ha hb i)
    (by
      have hlen : (n+1).bits.length ≤ width N W := by
        have h := nat_bits_le_self (n+1)
        unfold width
        nlinarith only [h,hn]
      cases signs (n+1) <;> simp [step,addTerm,NatAssign.Instruction.literalWidth,hlen])
  have hlen : (step (signs (n+1)) n).length ≤ 8 := by cases signs (n+1) <;> simp [step,addTerm]
  have hcoef : 3000*8^(step (signs (n+1)) n).length ≤ (2 : ℕ)^40 := by
    calc
      _ ≤ 3000*8^8 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hlen)
      _ ≤ _ := by norm_num
  refine ⟨c,t,he,hc.trans (hbound.trans (Nat.mul_le_mul_right _ hcoef)),⟨?_,hsc⟩,?_⟩
  · simpa only [step_values] using hbank
  · apply hf.mono
    cases signs (n+1) <;>
      simp [NatAssign.changes,step,addTerm,workspace,NatAssign.Instruction.target] <;> decide

#print axioms step_values
#print axioms step_executes

end Maxwell.Continuum.RationalTaylor
