import Maxwell.Cost.Structured.SignedBracketPlan

/-! Exact integer results and linear word growth for the bracket machine. -/
namespace Maxwell.Cost.Structured.SignedBracket
open NatAssign
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def midpointValue (b : ℕ) (v : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=6 then v b+v (b+3)
  else if k=7 then v (b+1)+v (b+4)
  else if k=8 then 2*v (b+2)
  else if k=9 then 2 else v (b+k)

def stepValue (b : ℕ) (negative : Bool) (v : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=0 then if negative then 64*v b else 33*v b+31*v (b+3)
  else if k=1 then if negative then 64*v (b+1) else 33*v (b+1)+31*v (b+4)
  else if k=2 then 64*v (b+2)
  else if k=3 then if negative then 31*v b+33*v (b+3) else 64*v (b+3)
  else if k=4 then if negative then 31*v (b+1)+33*v (b+4) else 64*v (b+4)
  else if k=5 then 64*v (b+2)
  else if k=9 then 64
  else if k=10 then 31*(if negative then v b else v (b+3))
  else if k=11 then 31*(if negative then v (b+1) else v (b+4))
  else v (b+k)

theorem midpoint_get (b : ℕ) (v : ℕ→ℕ) (k : ℕ) (hk : k<12) :
    values (midpointPlan b) v (b+k)=midpointValue b v k := by
  interval_cases k <;> simp [midpointPlan,values,Instruction.update,Instruction.target,
    Instruction.value,midpointValue,Nat.add_comm]

theorem step_get (b : ℕ) (negative : Bool) (v : ℕ→ℕ) (k : ℕ) (hk : k<12) :
    values (stepPlan b negative) v (b+k)=stepValue b negative v k := by
  cases negative <;> interval_cases k <;>
    simp [stepPlan,values,Instruction.update,Instruction.target,Instruction.value,stepValue,
      Nat.add_comm]

private theorem bits_of_bound {n B : ℕ} (h : n≤64*2^B) : n.bits.length≤B+7 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<(2:ℕ)^B := by positivity
  rw [pow_add]
  norm_num
  omega

theorem midpoint_width (b B : ℕ) (v : ℕ→ℕ)
    (hw : ∀i∈ids b,(v i).bits.length≤B) :
    ∀i∈ids b,(values (midpointPlan b) v i).bits.length≤B+7 := by
  have bound (k : ℕ) (hk : k<12) : v (b+k)≤2^B := by
    have h:=hw (b+k) (by simp only [ids,Finset.mem_Ico];omega)
    rw [Nat.size_eq_bits_len] at h
    exact (Nat.size_le.mp h).le
  intro i hi
  have range : b≤ i ∧ i<b+12 := Finset.mem_Ico.mp hi
  let k:=i-b
  have hk : k<12 := by dsimp [k];omega
  have eq : i=b+k := by dsimp [k];omega
  rw [eq,midpoint_get b v k hk]
  apply bits_of_bound
  have h0:=bound 0 (by decide)
  have h1:=bound 1 (by decide)
  have h2:=bound 2 (by decide)
  have h3:=bound 3 (by decide)
  have h4:=bound 4 (by decide)
  have hi:=bound k hk
  have hp : 0<(2:ℕ)^B := by positivity
  simp only [Nat.add_zero] at h0
  unfold midpointValue
  split_ifs <;> omega

theorem step_width (b B : ℕ) (negative : Bool) (v : ℕ→ℕ)
    (hw : ∀i∈ids b,(v i).bits.length≤B) :
    ∀i∈ids b,(values (stepPlan b negative) v i).bits.length≤B+7 := by
  have bound (k : ℕ) (hk : k<12) : v (b+k)≤2^B := by
    have h:=hw (b+k) (by simp only [ids,Finset.mem_Ico];omega)
    rw [Nat.size_eq_bits_len] at h
    exact (Nat.size_le.mp h).le
  intro i hi
  have range : b≤ i ∧ i<b+12 := Finset.mem_Ico.mp hi
  let k:=i-b
  have hk : k<12 := by dsimp [k];omega
  have eq : i=b+k := by dsimp [k];omega
  rw [eq,step_get b negative v k hk]
  apply bits_of_bound
  have h0:=bound 0 (by decide)
  have h1:=bound 1 (by decide)
  have h2:=bound 2 (by decide)
  have h3:=bound 3 (by decide)
  have h4:=bound 4 (by decide)
  have hi:=bound k hk
  have hp : 0<(2:ℕ)^B := by positivity
  simp only [Nat.add_zero] at h0
  cases negative <;> simp only [stepValue,Bool.false_eq_true,ite_false,ite_true] <;>
    split_ifs <;> omega

#print axioms midpoint_width
#print axioms step_width
end Maxwell.Cost.Structured.SignedBracket
