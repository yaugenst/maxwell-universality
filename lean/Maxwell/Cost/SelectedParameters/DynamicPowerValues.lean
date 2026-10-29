import Maxwell.Cost.SelectedParameters.GeometricValues
import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.SelectedParameters.DynamicPower
open Structured RationalAccumulator

def ids : Finset ℕ := {530,531,532,533}
def workspace : Finset ℕ := {0,1,2,3,532,533,534}
def initialization : List NatAssign.Instruction := [.literal 532 1,.literal 533 1]
def advance : List NatAssign.Instruction := [.multiply 530 532,.multiply 531 533]

def values (a b n : ℕ) (i : ℕ) : ℕ :=
  if i=530 then a else if i=531 then b else if i=532 then a^n else if i=533 then b^n else 0

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem initialization_valid : ∀ inst  ∈  initialization, inst.Valid ids := by
  simp [initialization,NatAssign.Instruction.Valid,ids]

theorem advance_valid : ∀ inst  ∈  advance, inst.Valid ids := by
  simp [advance,NatAssign.Instruction.Valid,ids]

theorem initialization_values (v : ℕ → ℕ) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values initialization v i=values (v 530) (v 531) 0 i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals simp [initialization,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values]

theorem advance_values (a b n : ℕ) :
    NatAssign.values advance (values a b n)=values a b (n+1) := by
  ext i
  by_cases h1 : i=532
  · subst i
    simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  by_cases h2 : i=533
  · subst i
    simp [advance,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm]
  simp [advance,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,h1,h2]

def width (N B : ℕ) : ℕ := (N+1)*(B+1)

theorem values_width (a b n N B : ℕ) (hn : n ≤ N)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B) (i : ℕ) :
    (values a b n i).bits.length ≤ width N B := by
  have hB : B ≤ width N B := by dsimp [width]; nlinarith
  have hpa : (a^n).bits.length ≤ width N B := by
    have hp := Geometric.power_bits a n
    have hm := Nat.mul_le_mul hn ha
    dsimp [width]
    nlinarith only [hp,hm]
  have hpb : (b^n).bits.length ≤ width N B := by
    have hp := Geometric.power_bits b n
    have hm := Nat.mul_le_mul hn hb
    dsimp [width]
    nlinarith only [hp,hm]
  simp only [values]
  split_ifs <;> first | exact ha.trans hB | exact hb.trans hB | exact hpa | exact hpb | simp

structure Ready (a b n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b n) s.val
  scratch : NatAssign.Scratch s.val

theorem Ready.stable {a b n : ℕ} {s t : Store} (hf : CountedShifted.Frame 534 s t)
    (hs : Ready a b n s) : Ready a b n t := by
  refine ⟨?_,?_⟩
  · intro i hi
    have hne : i ≠ 534 := by simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega
    exact word_of_eq (hf.2.2.2.2.2.1 i hne) (hs.bank i hi)
  · intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by omega)) (hs.scratch i hi)

theorem counter_frame {s t : Store} (hf : CountedShifted.Frame 534 s t) :
    BinaryPrecision.Frame workspace s.val t.val := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  exact hf.2.2.2.2.2.1 i (by simp only [workspace,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; omega)

end Maxwell.Cost.SelectedParameters.DynamicPower
