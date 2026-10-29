import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Realization.Spacing

namespace Maxwell.Cost.SelectedParameters.Geometric
open Structured

def extra : Finset ℕ := {520,521,522,523,524,525,526,527}
def ids : Finset ℕ := extra ∪ {30,31,32,33,34,35,36}
def workspace : Finset ℕ := {0,1,2,3,30,31,32,33,34,35,36,524,525,526,527}

def values (a b c d n : ℕ) (i : ℕ) : ℕ :=
  if i=520 then a else if i=521 then b else if i=30 ∨ i=522 then c else
  if i=31 ∨ i=523 then d else if i=32 ∨ i=524 then a^n else
  if i=33 ∨ i=525 then b^n else if i=526 then n else if i=527 then 1 else 0

def advance : List NatAssign.Instruction :=
  [.multiply 520 524,.multiply 521 525,.add 527 526,.copy 524 32,.copy 525 33]

def initialization : List NatAssign.Instruction :=
  [.literal 524 1,.literal 525 1,.literal 526 0,.literal 527 1,
   .copy 522 30,.copy 523 31,.literal 32 1,.literal 33 1,
   .literal 34 0,.literal 35 0,.literal 36 0]

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,extra,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem advance_valid : ∀ inst ∈ advance, inst.Valid ids := by
  simp [advance,NatAssign.Instruction.Valid,ids,extra]
theorem initialization_valid : ∀ inst ∈ initialization, inst.Valid ids := by
  simp [initialization,NatAssign.Instruction.Valid,ids,extra]

theorem advance_values (a b c d n : ℕ) :
    NatAssign.values advance (values a b c d n) = values a b c d (n+1) := by
  funext i
  by_cases h32 : i=32
  · subst i; simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h33 : i=33
  · subst i; simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h524 : i=524
  · subst i; simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h525 : i=525
  · subst i; simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h526 : i=526
  · subst i; simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,Nat.add_comm]
  simp [advance,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,
    h32,h33,h524,h525,h526]

theorem initialization_values (v : ℕ → ℕ) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values initialization v i = values (v 520) (v 521) (v 522) (v 523) 0 i := by
  simp only [ids,extra,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [initialization,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.value,NatAssign.Instruction.target,values]
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [initialization,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values]

theorem power_bits (a n : ℕ) : (a^n).bits.length ≤ n*a.bits.length+1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h := RationalAccumulator.bits_mul_le (a^n) a
    simp only [Nat.succ_mul]
    omega

/-- The fixed geometric base contributes linearly in the number of
iterations; runtime target words contribute only their original width. -/
def width (N A B : ℕ) : ℕ := (N+1)*(A+1)+B

theorem values_width (a b c d n N A B : ℕ) (hn : n ≤ N)
    (ha : a.bits.length ≤ A) (hb : b.bits.length ≤ A)
    (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) (i : ℕ) :
    (values a b c d n i).bits.length ≤ width N A B := by
  have hwA : A ≤ width N A B := by dsimp [width]; nlinarith
  have hwB : B ≤ width N A B := by dsimp [width]; omega
  have hpA : (a^n).bits.length ≤ width N A B := by
    have hp := power_bits a n
    have hm := Nat.mul_le_mul hn ha
    dsimp [width]; nlinarith
  have hpB : (b^n).bits.length ≤ width N A B := by
    have hp := power_bits b n
    have hm := Nat.mul_le_mul hn hb
    dsimp [width]; nlinarith
  have hnwidth : n.bits.length ≤ width N A B := by
    have hsize : n.bits.length ≤ n := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length n
    dsimp [width]; nlinarith
  have hone : 1 ≤ width N A B := by dsimp [width]; nlinarith
  simp only [values]
  split_ifs <;> first
    | exact ha.trans hwA | exact hb.trans hwA | exact hc.trans hwB | exact hd.trans hwB
    | exact hpA | exact hpB | exact hnwidth
    | (change 1 ≤ width N A B; exact hone) | simp

theorem rational_power (a b n : ℕ) :
    (a^n : ℕ)/(b^n : ℚ) = ((a:ℚ)/b)^n := by push_cast; rw [div_pow]

end Maxwell.Cost.SelectedParameters.Geometric
