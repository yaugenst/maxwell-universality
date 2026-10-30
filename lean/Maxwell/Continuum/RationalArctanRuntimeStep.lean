import Maxwell.Continuum.RationalArctanProgram
import Maxwell.Continuum.RationalTaylorRuntimeCycle

/-! The alternating arctangent evaluator reads its odd denominator factor
from a runtime word. Its step code contains only fixed literals. -/
namespace Maxwell.Continuum.RationalArctan.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def ids : Finset ℕ := RationalArctan.ids∪{619,628}
def workspace : Finset ℕ := RationalArctan.workspace∪{619,628}
def values (a b n i : ℕ) : ℕ :=
  if i=619 then 2*n+1 else if i=628 then 2 else RationalArctan.values a b negativeSigns n i
def step (sign : Sign) : List NatAssign.Instruction :=
  [.copy 615 617,.multiply 614 617,.copy 619 618,.multiply 616 618,
   .multiply 618 612,.multiply 618 613,.multiply 618 614]++RationalArctan.addTerm sign++
  [.multiply 610 615,.multiply 610 615,.multiply 611 616,.multiply 611 616,
   .literal 617 0,.literal 618 0,.add 628 619]

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega
theorem step_valid (sign : Sign) : ∀a∈step sign,a.Valid ids := by
  cases sign <;> simp [step,RationalArctan.addTerm,NatAssign.Instruction.Valid,ids,RationalArctan.ids]

theorem step_values (a b n : ℕ) :
    NatAssign.values (step (negativeSigns n)) (values a b n)=values a b (n+1) := by
  ext i
  by_cases h2 : i=612
  · subst i
    cases h : negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values,RationalArctan.numerator,termDenominator,h,
      Sign.positive,Sign.negative,Nat.mul_comm,Nat.add_comm]
  by_cases h3 : i=613
  · subst i
    cases h : negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values,RationalArctan.numerator,termDenominator,h,
      Sign.positive,Sign.negative,Nat.mul_comm,Nat.add_comm]
  by_cases h4 : i=614
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values,RationalArctan.denominator,termDenominator]
  by_cases h5 : i=615
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values,show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add,pow_two] <;> ring
  by_cases h6 : i=616
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values,show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add,pow_two] <;> ring
  by_cases h7 : i=617
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values]
  by_cases h8 : i=618
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values]
  by_cases h9 : i=619
  · subst i
    cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      values,RationalArctan.values] <;> omega
  cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    values,RationalArctan.values,h2,h3,h4,h5,h6,h7,h8,h9]

theorem values_width (a b n N W : ℕ) (hn : n≤N) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) : (values a b n i).bits.length≤RationalArctan.width N W := by
  have h2 : 2≤RationalArctan.width N W := by
    calc
      _ ≤ termWidth N W+2 := by omega
      _ ≤ (N+1)*(termWidth N W+2) := Nat.le_mul_of_pos_left _ (by omega)
  have hodd : (2*n+1).bits.length≤RationalArctan.width N W := by
    have h := nat_bits_le_self (2*n+1)
    unfold RationalArctan.width termWidth
    nlinarith only [h,hn,Nat.zero_le (N*W),Nat.zero_le (N*N*W),Nat.zero_le (N*N)]
  unfold values
  split_ifs
  · exact hodd
  · simpa only [show (2:ℕ).bits.length=2 by decide] using h2
  · exact RationalArctan.values_width a b negativeSigns n N W hn ha hb i

structure Ready (a b n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b n) s.val
  scratch : NatAssign.Scratch s.val

theorem step_executes (a b n N W : ℕ) (hn : n<N) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready a b n s) :
    ∃cost t,Executes input tape (NatAssign.code (step (negativeSigns n))) cost s t ∧
      cost≤2^64*(RationalArctan.width N W+2)^2 ∧ Ready a b (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,hb',hs',hf⟩ := NatAssign.executes ids ids_ge (step (negativeSigns n))
    (step_valid _) (values a b n) input tape s hs.bank hs.scratch
  have hp := NatAssign.price_bound ids (step (negativeSigns n)) (step_valid _) (values a b n)
    (RationalArctan.width N W) (fun i _ => values_width a b n N W hn.le ha hb i)
    (by cases negativeSigns n <;> simp [step,RationalArctan.addTerm,NatAssign.Instruction.literalWidth])
  have hlen : (step (negativeSigns n)).length≤15 := by cases negativeSigns n <;> simp [step,RationalArctan.addTerm]
  have hcoef : 3000*8^(step (negativeSigns n)).length≤2^64 := by
    calc
      _ ≤ 3000*8^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hlen)
      _ ≤ _ := by norm_num
  refine ⟨cost,t,he,hc.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),⟨?_,hs'⟩,?_⟩
  · simpa only [step_values] using hb'
  · apply hf.mono
    cases negativeSigns n <;> simp [NatAssign.changes,step,RationalArctan.addTerm,
      workspace,RationalArctan.workspace,NatAssign.Instruction.target] <;> decide

#print axioms step_executes
end Maxwell.Continuum.RationalArctan.Runtime
