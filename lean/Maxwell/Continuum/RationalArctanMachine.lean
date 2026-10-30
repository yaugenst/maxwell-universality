import Maxwell.Continuum.RationalArctanData
import Maxwell.Cost.Structured.Correctness

/-! Actual stored-word evaluation of the rational arctangent series. -/

namespace Maxwell.Continuum.RationalArctan
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2000000

def ids : Finset ℕ := {610,611,612,613,614,615,616,617,618}
def workspace : Finset ℕ := {0,1,2,3,612,613,614,615,616,617,618}

def values (a b : ℕ) (signs : ℕ→Sign) (n i : ℕ) : ℕ :=
  if i=610 then a else if i=611 then b else
  if i=612 then numerator a b (fun k => (signs k).positive) n else
  if i=613 then numerator a b (fun k => (signs k).negative) n else
  if i=614 then denominator b n else
  if i=615 then a^(2*n+1) else if i=616 then b^(2*n+1) else 0

def initialization : List NatAssign.Instruction :=
  [.literal 612 0,.literal 613 0,.literal 614 1,.copy 610 615,.copy 611 616,
   .literal 617 0,.literal 618 0]

def addTerm : Sign→List NatAssign.Instruction
  | .zero => [] | .plus => [.add 617 612] | .minus => [.add 617 613]

def step (s : Sign) (n : ℕ) : List NatAssign.Instruction :=
  [.copy 615 617,.multiply 614 617,.literal 618 (2*n+1),.multiply 616 618,
   .multiply 618 612,.multiply 618 613,.multiply 618 614]++addTerm s++
  [.multiply 610 615,.multiply 610 615,.multiply 611 616,.multiply 611 616,
   .literal 617 0,.literal 618 0]

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem initialization_valid : ∀ a ∈ initialization, a.Valid ids := by
  simp [initialization,NatAssign.Instruction.Valid,ids]

theorem step_valid (s : Sign) (n : ℕ) : ∀ a ∈ step s n, a.Valid ids := by
  cases s <;> simp [step,addTerm,NatAssign.Instruction.Valid,ids]

theorem initialization_values (v : ℕ→ℕ) (signs : ℕ→Sign) (i : ℕ) (hi : i∈ids) :
    NatAssign.values initialization v i=values (v 610) (v 611) signs 0 i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [initialization,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,denominator]

theorem step_values (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) :
    NatAssign.values (step (signs n) n) (values a b signs n)=values a b signs (n+1) := by
  ext i
  by_cases h2 : i=612
  · subst i
    cases h : signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,termDenominator,h,
      Sign.positive,Sign.negative,Nat.mul_comm,Nat.add_comm]
  by_cases h3 : i=613
  · subst i
    cases h : signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,numerator,termDenominator,h,
      Sign.positive,Sign.negative,Nat.mul_comm,Nat.add_comm]
  by_cases h4 : i=614
  · subst i
    cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,denominator,termDenominator]
  by_cases h5 : i=615
  · subst i
    cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,
      show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add,pow_two] <;> ring
  by_cases h6 : i=616
  · subst i
    cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,
      show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add,pow_two] <;> ring
  by_cases h7 : i=617
  · subst i
    cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values]
  by_cases h8 : i=618
  · subst i
    cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values]
  cases signs n <;> simp [step,addTerm,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,h2,h3,h4,h5,h6,h7,h8]

theorem values_width (a b : ℕ) (signs : ℕ→Sign) (n N W : ℕ) (hn : n≤N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (values a b signs n i).bits.length≤width N W := by
  have hT : W≤termWidth N W := by unfold termWidth; nlinarith
  have hwide : termWidth N W≤width N W := by unfold width; nlinarith
  have hnum (keep : ℕ→Bool) : (numerator a b keep n).bits.length≤width N W := by
    have hp := (numerator_bits a b keep n N W hn ha hb).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
    unfold width
    nlinarith only [hp]
  have hd : (denominator b n).bits.length≤width N W := by
    have hp := (denominator_bits b n N W hn hb).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
    unfold width
    nlinarith only [hp]
  simp only [values]
  split_ifs <;> first
    | exact ha.trans (hT.trans hwide)
    | exact hb.trans (hT.trans hwide)
    | exact hnum _
    | exact hd
    | exact (power_bits a n N W hn ha).trans hwide
    | exact (power_bits b n N W hn hb).trans hwide
    | simp

structure Ready (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b signs n) s.val
  scratch : NatAssign.Scratch s.val

theorem step_executes (a b : ℕ) (signs : ℕ→Sign) (n N W : ℕ) (hn : n<N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready a b signs n s) :
    ∃ cost t, Executes input tape (NatAssign.code (step (signs n) n)) cost s t ∧
      cost≤2^60*(width N W+2)^2 ∧ Ready a b signs (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,t,he,hc,hbank,hsc,hf⟩ := NatAssign.executes ids ids_ge (step (signs n) n)
    (step_valid _ _) (values a b signs n) input tape s hs.bank hs.scratch
  have hbound := NatAssign.price_bound ids (step (signs n) n) (step_valid _ _)
    (values a b signs n) (width N W) (fun i _ => values_width a b signs n N W hn.le ha hb i)
    (by
      have hlen : (2*n+1).bits.length≤width N W := by
        have h := RationalTaylor.nat_bits_le_self (2*n+1)
        unfold width termWidth
        nlinarith only [h,hn,Nat.zero_le (N*W),Nat.zero_le (N^2*W)]
      have hbits : n.bits.length<width N W := by simpa using hlen
      cases signs n <;> simp [step,addTerm,NatAssign.Instruction.literalWidth,hbits])
  have hlen : (step (signs n) n).length≤14 := by cases signs n <;> simp [step,addTerm]
  have hcoef : 3000*8^(step (signs n) n).length≤(2:ℕ)^60 := by
    calc
      _ ≤ 3000*8^14 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hlen)
      _ ≤ _ := by norm_num
  refine ⟨c,t,he,hc.trans (hbound.trans (Nat.mul_le_mul_right _ hcoef)),⟨?_,hsc⟩,?_⟩
  · simpa only [step_values] using hbank
  · apply hf.mono
    cases signs n <;>
      simp [NatAssign.changes,step,addTerm,workspace,NatAssign.Instruction.target] <;> decide

#print axioms step_values
#print axioms step_executes

end Maxwell.Continuum.RationalArctan
