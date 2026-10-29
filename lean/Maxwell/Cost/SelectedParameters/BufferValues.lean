import Maxwell.Cost.SelectedParameters.RationalPower
import Maxwell.Realization.Buffer

/-! Stored integer values for the exact buffer stopping test. No selected
scalar or stopping index is embedded in the executable instruction list. -/
namespace Maxwell.Cost.SelectedParameters.Buffer
open Structured RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

structure Data where
  a : ℕ
  b : ℕ
  u : ℕ
  v : ℕ
  e : ℕ
  f : ℕ
  m : ℕ
  s : ℕ
  deriving Repr

def Data.Bounded (d : Data) (B : ℕ) : Prop :=
  d.a.bits.length ≤ B ∧ d.b.bits.length ≤ B ∧ d.u.bits.length ≤ B ∧ d.v.bits.length ≤ B ∧
  d.e.bits.length ≤ B ∧ d.f.bits.length ≤ B ∧ d.m.bits.length ≤ B ∧ d.s.bits.length ≤ B

def base : Finset ℕ := {560,561,562,563,564,565,566,567,568,569,570,571}
def ids : Finset ℕ := base ∪ {572,573,574,575,576,577,578,579,30,31,32,33,34,35,36}
def workspace : Finset ℕ := {0,1,2,3,30,31,32,33,34,35,36,568,569,570,571,572,573,574,575,576,577,578,579}

def polynomial (d : Data) (n : ℕ) : ℕ := d.m*d.f+d.e*(d.s+n+1)^3
def left (d : Data) (n : ℕ) : ℕ := d.u*(polynomial d n)^2*d.a^n
def right (d : Data) (n : ℕ) : ℕ := d.v*d.f^2*d.b^n
def Test (d : Data) (n : ℕ) : Prop := left d n ≤ right d n
instance (d : Data) : DecidablePred (Test d) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def values (d : Data) (n i : ℕ) : ℕ :=
  if i=560 then d.a else if i=561 then d.b else if i=562 then d.u else if i=563 then d.v else
  if i=564 then d.e else if i=565 then d.f else if i=566 then d.m else if i=567 then d.s else
  if i=568 then d.a^n else if i=569 then d.b^n else if i=570 then n else if i=571 then 1 else
  if i=572 then d.s+n+1 else if i=573 then (d.s+n+1)^2 else if i=574 then (d.s+n+1)^3 else
  if i=575 then d.e*(d.s+n+1)^3 else if i=576 then d.m*d.f else
  if i=577 then polynomial d n else if i=578 then (polynomial d n)^2 else
  if i=579 ∨ i=32 then left d n else if i=30 then right d n else if i=31 ∨ i=33 then 1 else 0

def recompute : List NatAssign.Instruction :=
  [.copy 567 572,.add 570 572,.add 571 572,
   .copy 572 573,.multiply 572 573,.copy 573 574,.multiply 572 574,
   .copy 574 575,.multiply 564 575,.copy 566 576,.multiply 565 576,
   .copy 575 577,.add 576 577,.copy 577 578,.multiply 577 578,
   .copy 578 579,.multiply 562 579,.multiply 568 579,
   .copy 565 30,.multiply 565 30,.multiply 563 30,.multiply 569 30,
   .copy 579 32,.literal 31 1,.literal 33 1,.literal 34 0,.literal 35 0,.literal 36 0]

def advancePrefix : List NatAssign.Instruction :=
  [.multiply 560 568,.multiply 561 569,.add 571 570]
def advance : List NatAssign.Instruction := advancePrefix ++ recompute

def initializePrefix : List NatAssign.Instruction :=
  [.literal 568 1,.literal 569 1,.literal 570 0,.literal 571 1]
def initialization : List NatAssign.Instruction := initializePrefix ++ recompute

def initialData (v : ℕ → ℕ) : Data := ⟨v 560,v 561,v 562,v 563,v 564,v 565,v 566,v 567⟩

theorem values_append (xs ys : List NatAssign.Instruction) (v : ℕ → ℕ) :
    NatAssign.values (xs++ys) v = NatAssign.values ys (NatAssign.values xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (x.update v)

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,base,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem recompute_valid : ∀ inst ∈ recompute, inst.Valid ids := by
  simp [recompute,NatAssign.Instruction.Valid,ids,base]
theorem advance_valid : ∀ inst ∈ advance, inst.Valid ids := by
  simp only [advance,List.mem_append]
  intro inst hi
  rcases hi with hi | hi
  · simp only [advancePrefix,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [NatAssign.Instruction.Valid,ids,base]
  · exact recompute_valid inst hi
theorem initialization_valid : ∀ inst ∈ initialization, inst.Valid ids := by
  simp only [initialization,List.mem_append]
  intro inst hi
  rcases hi with hi | hi
  · simp only [initializePrefix,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [NatAssign.Instruction.Valid,ids,base]
  · exact recompute_valid inst hi

theorem recompute_values (d : Data) (n : ℕ) (v : ℕ → ℕ)
    (hv : ∀ i ∈ base, v i = values d n i) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values recompute v i = values d n i := by
  have h562 := hv 562 (by simp [base])
  have h563 := hv 563 (by simp [base])
  have h564 := hv 564 (by simp [base])
  have h565 := hv 565 (by simp [base])
  have h566 := hv 566 (by simp [base])
  have h567 := hv 567 (by simp [base])
  have h568 := hv 568 (by simp [base])
  have h569 := hv 569 (by simp [base])
  have h570 := hv 570 (by simp [base])
  have h571 := hv 571 (by simp [base])
  simp only [ids,base,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [recompute,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target] using (hv _ (by simp [base]))
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [recompute,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,h562,h563,h564,h565,
      h566,h567,h568,h569,h570,h571,values,polynomial,left,right] <;> ring_nf <;> simp

theorem advance_values (d : Data) (n i : ℕ) (hi : i ∈ ids) :
    NatAssign.values advance (values d n) i = values d (n+1) i := by
  rw [advance,values_append]
  apply recompute_values d (n+1) _ _ i hi
  intro j hj
  simp only [base,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [advancePrefix,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,pow_succ,Nat.mul_comm,Nat.add_comm]

theorem initialization_values (v : ℕ → ℕ) (i : ℕ) (hi : i ∈ ids) :
    NatAssign.values initialization v i = values (initialData v) 0 i := by
  rw [initialization,values_append]
  apply recompute_values (initialData v) 0 _ _ i hi
  intro j hj
  simp only [base,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [initializePrefix,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,values,initialData]

def width (N B : ℕ) : ℕ := (N+1)*(B+1)+10*(B+N+2)

theorem width_one (N B : ℕ) : 1 ≤ width N B := by dsimp [width]; nlinarith

theorem values_width (d : Data) (n N B : ℕ) (hn : n ≤ N) (hd : d.Bounded B) (i : ℕ) :
    (values d n i).bits.length ≤ width N B := by
  rcases hd with ⟨ha,hb,hu,hv,he,hf,hm,hs⟩
  have hnsize : n.bits.length ≤ N := by
    have hsize : n.bits.length ≤ n := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length n
    omega
  have hta := bits_add_le d.s n
  have htb := bits_add_le (d.s+n) 1
  have ht : (d.s+n+1).bits.length ≤ B+N+2 := by norm_num at htb; omega
  have ht2 := Rational.power_bits 2 (d.s+n+1) (B+N+2) ht
  have ht3 := Rational.power_bits 3 (d.s+n+1) (B+N+2) ht
  have he3 := bits_mul_le d.e ((d.s+n+1)^3)
  have hmf := bits_mul_le d.m d.f
  have hp := bits_add_le (d.m*d.f) (d.e*(d.s+n+1)^3)
  have hp' : (polynomial d n).bits.length ≤ 2*B+3*(B+N+2)+2 := by
    dsimp only [polynomial]
    omega
  have hp2 := Rational.power_bits 2 (polynomial d n) (2*B+3*(B+N+2)+2) hp'
  have haPow := Rational.power_bits n d.a B ha
  have hbPow := Rational.power_bits n d.b B hb
  have hf2 := Rational.power_bits 2 d.f B hf
  have hleft1 := bits_mul_le d.u ((polynomial d n)^2)
  have hleft2 := bits_mul_le (d.u*(polynomial d n)^2) (d.a^n)
  have hright1 := bits_mul_le d.v (d.f^2)
  have hright2 := bits_mul_le (d.v*d.f^2) (d.b^n)
  have hnB := Nat.mul_le_mul_right B hn
  have hwB : B ≤ width N B := by dsimp [width]; nlinarith
  have hwt : (d.s+n+1).bits.length ≤ width N B := by dsimp [width]; nlinarith only [ht]
  have hwt2 : ((d.s+n+1)^2).bits.length ≤ width N B := by dsimp [width]; nlinarith only [ht2]
  have hwt3 : ((d.s+n+1)^3).bits.length ≤ width N B := by dsimp [width]; nlinarith only [ht3]
  have hwe3 : (d.e*(d.s+n+1)^3).bits.length ≤ width N B := by dsimp [width]; nlinarith only [he3,he,ht3]
  have hwmf : (d.m*d.f).bits.length ≤ width N B := by dsimp [width]; nlinarith only [hmf,hm,hf]
  have hwp : (polynomial d n).bits.length ≤ width N B := by dsimp [width]; nlinarith only [hp']
  have hwp2 : ((polynomial d n)^2).bits.length ≤ width N B := by dsimp [width]; nlinarith only [hp2]
  have hwleft : (left d n).bits.length ≤ width N B := by dsimp [left,width]; nlinarith only [hleft1,hleft2,hu,hp2,haPow,hnB]
  have hwright : (right d n).bits.length ≤ width N B := by dsimp [right,width]; nlinarith only [hright1,hright2,hv,hf2,hbPow,hnB]
  have hwa : (d.a^n).bits.length ≤ width N B := by dsimp [width]; nlinarith only [haPow,hnB]
  have hwb : (d.b^n).bits.length ≤ width N B := by dsimp [width]; nlinarith only [hbPow,hnB]
  have hwn : n.bits.length ≤ width N B := by dsimp [width]; nlinarith only [hnsize]
  have hw1 : (1:ℕ).bits.length ≤ width N B := by simpa using width_one N B
  have hite (p : Prop) [Decidable p] (x y : ℕ)
      (hx : x.bits.length ≤ width N B) (hy : y.bits.length ≤ width N B) :
      (if p then x else y).bits.length ≤ width N B := by split <;> assumption
  unfold values
  apply hite _ _ _ (ha.trans hwB)
  apply hite _ _ _ (hb.trans hwB)
  apply hite _ _ _ (hu.trans hwB)
  apply hite _ _ _ (hv.trans hwB)
  apply hite _ _ _ (he.trans hwB)
  apply hite _ _ _ (hf.trans hwB)
  apply hite _ _ _ (hm.trans hwB)
  apply hite _ _ _ (hs.trans hwB)
  apply hite _ _ _ hwa
  apply hite _ _ _ hwb
  apply hite _ _ _ hwn
  apply hite _ _ _ hw1
  apply hite _ _ _ hwt
  apply hite _ _ _ hwt2
  apply hite _ _ _ hwt3
  apply hite _ _ _ hwe3
  apply hite _ _ _ hwmf
  apply hite _ _ _ hwp
  apply hite _ _ _ hwp2
  apply hite _ _ _ hwleft
  apply hite _ _ _ hwright
  apply hite _ _ _ hw1
  simp

end Maxwell.Cost.SelectedParameters.Buffer
