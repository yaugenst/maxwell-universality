import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.RationalAccumulator.Move
import Mathlib.Data.Nat.Log

namespace Maxwell.Cost.WeightedSource.Metadata
open Structured
set_option maxHeartbeats 1800000

def precision (n b : ℕ) : ℕ := b+Nat.clog 2 (n+1)
def prePlan (n : ℕ) : List NatAssign.Instruction :=
  [.literal 403 2,.copy 401 400,.multiply 403 400,.literal 403 5,.add 403 400,
   .copy 401 402,.literal 403 (Nat.clog 2 (n+1)),.add 403 402,
   .copy 402 514,.literal 403 2,.add 403 514,
   .copy 402 408,.literal 403 1,.add 403 408,
   .copy 251 510,.copy 514 511,.literal 403 n,.multiply 403 511,.add 251 511,
   .copy 402 513,.copy 510 270,.copy 511 271,.copy 513 273,.literal 403 0]

def postPlan : List NatAssign.Instruction :=
  [.copy 412 512,.copy 512 272,.copy 512 261,.copy 512 262,.literal 408 0]

def ids : Finset ℕ := {251,261,262,270,271,272,273,400,401,402,403,408,412,510,511,512,513,514,515}
def initial (b heapEnd : ℕ) (i : ℕ) : ℕ := if i=401 then b else if i=251 then heapEnd else 0

def preValues (n b heapEnd : ℕ) : ℕ→ℕ := NatAssign.values (prePlan n) (initial b heapEnd)
def powerValues (n b heapEnd : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (preValues n b heapEnd) 412 (2^precision n b)) 515 (2^(precision n b+1))
def resultValues (n b heapEnd : ℕ) : ℕ→ℕ := NatAssign.values postPlan (powerValues n b heapEnd)

def powerBudget (p : ℕ) : ℕ := (p+1)*(13*p.bits.length+25)+21*p.bits.length+27
def costBound (n b heapEnd : ℕ) : ℕ := NatAssign.price (prePlan n) (initial b heapEnd)+
  powerBudget (precision n b)+powerBudget (precision n b+1)+NatAssign.price postPlan (powerValues n b heapEnd)

@[simp] theorem pre_values (n b heapEnd : ℕ) :
    preValues n b heapEnd 400=2*b+5 ∧ preValues n b heapEnd 402=precision n b ∧
    preValues n b heapEnd 514=precision n b+2 ∧ preValues n b heapEnd 408=precision n b+1 ∧
    preValues n b heapEnd 412=0 ∧ preValues n b heapEnd 515=0 := by
  simp [preValues,prePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,initial,precision,Nat.add_comm,Nat.mul_comm]

/-- Exact public metadata values, including reusable U/V and local aliases. -/
theorem result_values (n b heapEnd : ℕ) :
    resultValues n b heapEnd 400=2*b+5 ∧ resultValues n b heapEnd 402=precision n b ∧
    resultValues n b heapEnd 514=precision n b+2 ∧ resultValues n b heapEnd 515=2^(precision n b+1) ∧
    resultValues n b heapEnd 412=2^precision n b ∧ resultValues n b heapEnd 510=heapEnd ∧
    resultValues n b heapEnd 511=heapEnd+n*(precision n b+2) ∧
    resultValues n b heapEnd 512=2^precision n b ∧ resultValues n b heapEnd 513=precision n b ∧
    resultValues n b heapEnd 270=heapEnd ∧ resultValues n b heapEnd 271=heapEnd+n*(precision n b+2) ∧
    resultValues n b heapEnd 272=2^precision n b ∧ resultValues n b heapEnd 273=precision n b ∧
    resultValues n b heapEnd 261=2^precision n b ∧ resultValues n b heapEnd 262=2^precision n b ∧
    resultValues n b heapEnd 403=0 ∧ resultValues n b heapEnd 408=0 := by
  simp [resultValues,powerValues,preValues,prePlan,postPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initial,precision,Nat.add_comm,Nat.mul_comm]

def widthBound (n b heapEnd : ℕ) : ℕ := precision n b+n.bits.length+heapEnd.bits.length+10

theorem bits_le_self (x : ℕ) : x.bits.length≤x := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=x))

theorem costBound_polynomial (n b heapEnd : ℕ) : costBound n b heapEnd≤200000*(widthBound n b heapEnd)^2 := by
  let c := Nat.clog 2 (n+1)
  let p := b+c
  have hb := bits_le_self b
  have hc := bits_le_self c
  have hp := bits_le_self p
  have hp1 := bits_le_self (p+1)
  have hp2 := bits_le_self (p+2)
  have h2b := RationalAccumulator.bits_mul_le 2 b
  have hk := RationalAccumulator.bits_add_le 5 (2*b)
  have hmul := RationalAccumulator.bits_mul_le n (2+p)
  have hadd := RationalAccumulator.bits_add_le heapEnd (n*(2+p))
  have hpow : (2^p:ℕ).bits.length=p+1 := by simp [PowerOfTwo.power_bits]
  have hpow1 : (2^(p+1):ℕ).bits.length=p+2 := by simp [PowerOfTwo.power_bits]
  have hpb : p=b+c := rfl
  have hcp : (c+b).bits.length≤p := by simpa only [p,Nat.add_comm] using hp
  have hcp2 : (2+(c+b)).bits.length≤p+2 := by simpa only [p,Nat.add_comm] using hp2
  have hmulp : (n*(2+(c+b))).bits.length≤n.bits.length+p+2 := by
    have h := RationalAccumulator.bits_mul_le n (2+(c+b))
    omega
  have haddp : (heapEnd+n*(2+(c+b))).bits.length≤heapEnd.bits.length+n.bits.length+p+3 := by
    have h := RationalAccumulator.bits_add_le heapEnd (n*(2+(c+b)))
    have hh : max heapEnd.bits.length (n*(2+(c+b))).bits.length≤heapEnd.bits.length+n.bits.length+p+2 :=
      max_le (by omega) (by omega)
    omega
  have hq1 : (2+b.bits.length+3)^2≤(p+n.bits.length+heapEnd.bits.length+10)^2 :=
    Nat.pow_le_pow_left (by dsimp only [p];omega) 2
  have hq2 : (n.bits.length+(2+(c+b)).bits.length+3)^2≤(p+n.bits.length+heapEnd.bits.length+10)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hbig : p+n.bits.length+heapEnd.bits.length+10≤(p+n.bits.length+heapEnd.bits.length+10)^2 :=
    Nat.le_self_pow (by decide) _
  have hpre : NatAssign.price (prePlan n) (initial b heapEnd)≤100000*(p+n.bits.length+heapEnd.bits.length+10)^2 := by
    simp [prePlan,NatAssign.price,NatAssign.Instruction.price,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    norm_num only [show (2:ℕ).bits.length=2 from rfl, show (5:ℕ).bits.length=3 from rfl] at h2b ⊢
    dsimp only [p,c] at *
    nlinarith
  have hpost : NatAssign.price postPlan (powerValues n b heapEnd)≤200*(p+2) := by
    simp [postPlan,powerValues,preValues,prePlan,NatAssign.price,NatAssign.values,NatAssign.Instruction.price,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    dsimp only [precision]
    have hpp : (2^(b+Nat.clog 2 (n+1)):ℕ).bits.length=p+1 := hpow
    have hpp1 : (1+(Nat.clog 2 (n+1)+b)).bits.length≤p+1 := by simpa only [p,c,Nat.add_comm] using hp1
    nlinarith
  have hpower : powerBudget p+powerBudget (p+1)≤200*(p+2)^2 := by
    dsimp only [powerBudget]
    nlinarith
  have hsq : (p+2)^2≤(p+n.bits.length+heapEnd.bits.length+10)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlin : p+2≤(p+n.bits.length+heapEnd.bits.length+10)^2 := by nlinarith
  dsimp only [costBound,widthBound]
  change _≤200000*(p+n.bits.length+heapEnd.bits.length+10)^2
  change _+powerBudget p+powerBudget (p+1)+_≤_
  nlinarith

end Maxwell.Cost.WeightedSource.Metadata
