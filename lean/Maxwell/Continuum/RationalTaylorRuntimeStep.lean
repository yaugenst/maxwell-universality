import Maxwell.Continuum.RationalTaylorProgram
import Maxwell.Continuum.RationalTaylorCenters
import Maxwell.Cost.Structured.RegisterFootprint
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! A fixed Taylor step reads the next factorial factor from a runtime
word. No precision-dependent integer literal appears in its instruction list. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def ids : Finset ℕ := RationalTaylor.ids∪{607,608}
def workspace : Finset ℕ := RationalTaylor.workspace∪{607,608}
def values (a b : ℕ) (signs : ℕ→Sign) (n i : ℕ) : ℕ :=
  if i=607 then n+1 else if i=608 then 1 else RationalTaylor.values a b signs n i
def step (sign : Sign) : List NatAssign.Instruction :=
  [.copy 607 606,.multiply 601 606,.multiply 606 602,.multiply 606 603,
   .multiply 606 604,.multiply 600 605]++RationalTaylor.addTerm sign++
   [.literal 606 0,.add 608 607]

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem step_valid (sign : Sign) : ∀a∈step sign,a.Valid ids := by
  cases sign <;> simp [step,RationalTaylor.addTerm,NatAssign.Instruction.Valid,ids,RationalTaylor.ids]

theorem step_values (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) :
    NatAssign.values (step (signs (n+1))) (values a b signs n)=values a b signs (n+1) := by
  ext i
  by_cases h2 : i=602
  · subst i
    cases h : signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values,numerator,h,Sign.positive,Sign.negative,pow_succ,
      Nat.mul_comm,Nat.add_comm]
  by_cases h3 : i=603
  · subst i
    cases h : signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values,numerator,h,Sign.positive,Sign.negative,pow_succ,
      Nat.mul_comm,Nat.add_comm]
  by_cases h4 : i=604
  · subst i
    cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values,denominator_succ]
  by_cases h5 : i=605
  · subst i
    cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values,pow_succ,Nat.mul_comm]
  by_cases h6 : i=606
  · subst i
    cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values]
  by_cases h7 : i=607
  · subst i
    cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalTaylor.values,Nat.add_comm]
  cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    values,RationalTaylor.values,h2,h3,h4,h5,h6,h7]

theorem values_width (a b : ℕ) (signs : ℕ→Sign) (n N W : ℕ) (hn : n≤N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (values a b signs n i).bits.length≤width N W := by
  have h1 : 1≤width N W := by unfold width;nlinarith
  have hnext : (n+1).bits.length≤width N W := by
    have h := nat_bits_le_self (n+1)
    unfold width
    nlinarith only [h,hn,Nat.zero_le (N*W),Nat.zero_le (N*N)]
  unfold values
  split_ifs
  · exact hnext
  · simpa using h1
  · exact RationalTaylor.values_width a b signs n N W hn ha hb i

structure Ready (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b signs n) s.val
  scratch : NatAssign.Scratch s.val

theorem step_executes (a b : ℕ) (signs : ℕ→Sign) (n N W : ℕ) (hn : n<N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready a b signs n s) :
    ∃cost t,Executes input tape (NatAssign.code (step (signs (n+1)))) cost s t ∧
      cost≤2^44*(width N W+2)^2 ∧ Ready a b signs (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,hb',hs',hf⟩ := NatAssign.executes ids ids_ge (step (signs (n+1)))
    (step_valid _) (values a b signs n) input tape s hs.bank hs.scratch
  have hp := NatAssign.price_bound ids (step (signs (n+1))) (step_valid _)
    (values a b signs n) (width N W) (fun i _ => values_width a b signs n N W hn.le ha hb i)
    (by cases signs (n+1) <;> simp [step,RationalTaylor.addTerm,NatAssign.Instruction.literalWidth])
  have hlen : (step (signs (n+1))).length≤9 := by cases signs (n+1) <;> simp [step,RationalTaylor.addTerm]
  have hcoef : 3000*8^(step (signs (n+1))).length≤2^44 := by
    calc
      _ ≤ 3000*8^9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hlen)
      _ ≤ _ := by norm_num
  refine ⟨cost,t,he,hc.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),⟨?_,hs'⟩,?_⟩
  · simpa only [step_values] using hb'
  · apply hf.mono
    cases signs (n+1) <;>
      simp [NatAssign.changes,step,RationalTaylor.addTerm,workspace,RationalTaylor.workspace,
        NatAssign.Instruction.target] <;> decide

theorem Ready.count_frame (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) {s t : Store}
    (hs : Ready a b signs n s) (hf : CountedShifted.Frame 609 s t) : Ready a b signs n t := by
  refine ⟨?_,?_⟩
  · intro i hi
    have hne : i≠609 := by
      simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact word_of_eq (hf.2.2.2.2.2.1 i hne) (hs.bank i hi)
  · intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by omega)) (hs.scratch i hi)

#print axioms step_executes
#print axioms Ready.count_frame
end Maxwell.Continuum.RationalTaylor.Runtime
