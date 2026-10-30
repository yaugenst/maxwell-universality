import Maxwell.Continuum.ProfileBufferLayout

/-! Charged fixed arithmetic for the actual buffer widths and addresses. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def allocationFirstWidth (B : ℕ) : ℕ := 2^25*(B+1)
def allocationSecondWidth (B : ℕ) : ℕ := 2^40*(B+1)
def allocationBound (B : ℕ) : ℕ := 2^64*(B+1)
def allocationArithmeticCode : Code := .seq (NatAssign.code bufferBudgetPlan)
  (.seq (NatAssign.code bufferWidthPlan) (NatAssign.code bufferAddressPlan))
def allocationArithmeticCost (B : ℕ) : ℕ := stageCost B+
  (stageCost (allocationFirstWidth B)+stageCost (allocationSecondWidth B))
def allocationArithmeticWorkspace : Finset ℕ := {0,1,2,3}∪allocationIds

theorem allocationIds_ge (i : ℕ) (hi : i∈allocationIds) : 4 ≤ i := by
  simp only [allocationIds,bufferIds,bufferHeaderIds,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton] at hi
  omega

theorem bufferInput_width (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (i : ℕ) :
    (bufferInput N D heap i).bits.length≤B := by
  unfold bufferInput
  split_ifs <;> first | exact hN | exact hD | exact hh | simp

theorem bufferBudgetPlan_literalWidth (B : ℕ) (hB : 501≤B) :
    ∀a∈bufferBudgetPlan,a.literalWidth≤B := by
  have h46 : ((2:ℕ)^46).bits.length=47 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  have h500 : ((2:ℕ)^500).bits.length=501 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  intro a ha
  simp only [bufferBudgetPlan,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [NatAssign.Instruction.literalWidth,h46,h500,
      show (1:ℕ).bits.length=1 from rfl,show (0:ℕ).bits.length=0 from rfl] <;> omega

theorem bufferBudgetValues_width (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (hB : 501≤B)
    (i : ℕ) (hi : i∈allocationIds) :
    (bufferBudgetValues N D heap i).bits.length≤allocationFirstWidth B := by
  have h := NatAssign.values_width_bound allocationIds bufferBudgetPlan bufferBudgetPlan_valid
    (bufferInput N D heap) B (fun i _=>bufferInput_width N D heap B hN hD hh i)
    (bufferBudgetPlan_literalWidth B hB) i hi
  change (bufferBudgetValues N D heap i).bits.length+1≤2^24*(B+1) at h
  unfold allocationFirstWidth
  omega

theorem bufferWidthPlan_literalWidth (B : ℕ) :
    ∀a∈bufferWidthPlan,a.literalWidth≤allocationFirstWidth B := by
  simp [bufferWidthPlan,NatAssign.Instruction.literalWidth,allocationFirstWidth,
    show (16:ℕ).bits.length=5 from rfl,show (96:ℕ).bits.length=7 from rfl,
    show (112:ℕ).bits.length=7 from rfl]
  omega

theorem bufferWidthValues_width (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (hB : 501≤B)
    (i : ℕ) (hi : i∈allocationIds) :
    (bufferWidthValues N D heap i).bits.length≤allocationSecondWidth B := by
  have h := NatAssign.values_width_bound allocationIds bufferWidthPlan bufferWidthPlan_valid
    (bufferBudgetValues N D heap) (allocationFirstWidth B)
    (bufferBudgetValues_width N D heap B hN hD hh hB)
    (bufferWidthPlan_literalWidth B) i hi
  change (bufferWidthValues N D heap i).bits.length+1≤2^11*(allocationFirstWidth B+1) at h
  unfold allocationFirstWidth at h
  unfold allocationSecondWidth
  omega

theorem bufferAddressValues_width (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (hB : 501≤B)
    (i : ℕ) (hi : i∈allocationIds) :
    (bufferAddressValues N D heap i).bits.length≤allocationBound B := by
  have h := NatAssign.values_width_bound allocationIds bufferAddressPlan bufferAddressPlan_valid
    (bufferWidthValues N D heap) (allocationSecondWidth B)
    (bufferWidthValues_width N D heap B hN hD hh hB)
    (by simp [bufferAddressPlan,NatAssign.Instruction.literalWidth]) i hi
  change (bufferAddressValues N D heap i).bits.length+1≤2^20*(allocationSecondWidth B+1) at h
  unfold allocationSecondWidth at h
  unfold allocationBound
  omega

theorem allocation_arithmetic_executes (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (hB : 501≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds (bufferInput N D heap) s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape allocationArithmeticCode cost s t ∧
      cost≤allocationArithmeticCost B ∧
      NatAssign.Bank allocationIds (bufferAddressValues N D heap) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame allocationArithmeticWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := fixedBankStage_executes allocationIds allocationIds_ge
    bufferBudgetPlan bufferBudgetPlan_valid (by decide) (bufferInput N D heap) B
    (fun i _=>bufferInput_width N D heap B hN hD hh i) (bufferBudgetPlan_literalWidth B hB)
    input tape s hs hz
  obtain ⟨c1,s1,e1,hc1,b1,z1,f1⟩ := fixedBankStage_executes allocationIds allocationIds_ge
    bufferWidthPlan bufferWidthPlan_valid (by decide) (bufferBudgetValues N D heap)
    (allocationFirstWidth B) (bufferBudgetValues_width N D heap B hN hD hh hB)
    (bufferWidthPlan_literalWidth B) input tape s0 b0 z0
  obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := fixedBankStage_executes allocationIds allocationIds_ge
    bufferAddressPlan bufferAddressPlan_valid (by decide) (bufferWidthValues N D heap)
    (allocationSecondWidth B) (bufferWidthValues_width N D heap B hN hD hh hB)
    (by simp [bufferAddressPlan,NatAssign.Instruction.literalWidth]) input tape s1 b1 z1
  exact ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold allocationArithmeticCost;omega,
    b2,z2,f0.trans (f1.trans f2)⟩

theorem allocationArithmeticCost_polynomial (B : ℕ) :
    allocationArithmeticCost B≤2^180*(B+2)^2 := by
  have first : stageCost (allocationFirstWidth B)≤2^148*(B+2)^2 := by
    unfold stageCost
    calc
      _≤2^96*(2^26*(B+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold allocationFirstWidth;omega) 2)
      _=_ := by ring
  have second : stageCost (allocationSecondWidth B)≤2^178*(B+2)^2 := by
    unfold stageCost
    calc
      _≤2^96*(2^41*(B+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold allocationSecondWidth;omega) 2)
      _=_ := by ring
  change 2^96*(B+2)^2+(stageCost (allocationFirstWidth B)+stageCost (allocationSecondWidth B))≤_
  omega

#print axioms allocation_arithmetic_executes
#print axioms allocationArithmeticCost_polynomial
end Maxwell.Continuum.Profile.Runtime
