import Maxwell.Continuum.ProfileCacheAllocation
import Maxwell.Continuum.CutoffMonomialCache

/-! Fixed arithmetic computes the exact two-buffer cache widths and disjoint
addresses from the degree, stored coefficient width, and free-memory cursor. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def cacheDimensionIds : Finset ℕ := Finset.Icc 720 729

def cacheWidthPlan : List NatAssign.Instruction :=
  [.copy 720 723,.literal 728 2,.multiply 728 723,.add 721 723,
   .literal 728 3,.add 728 723,.multiply 720 723,.add 721 723,
   .copy 720 724,.literal 728 8,.multiply 728 724,.add 724 723,
   .literal 728 17,.add 728 723,.literal 728 16,.multiply 728 723,
   .copy 720 724,.literal 728 1,.add 728 724,.literal 728 4,.multiply 728 724]

def cacheAddressPlan : List NatAssign.Instruction :=
  [.copy 724 725,.copy 723 726,.copy 722 727,.copy 724 729,
   .multiply 723 729,.literal 728 3,.multiply 728 729,.add 722 729]

def cacheDimensionInput (D W heap : ℕ) (i : ℕ) : ℕ :=
  if i=720 then D else if i=721 then W else if i=722 then heap else 0

def cacheWidthValues (D W heap : ℕ) : ℕ→ℕ := NatAssign.values cacheWidthPlan (cacheDimensionInput D W heap)
def cacheDimensionValues (D W heap : ℕ) : ℕ→ℕ := NatAssign.values cacheAddressPlan (cacheWidthValues D W heap)
def cacheNextBase (D W heap : ℕ) : ℕ := heap+3*(4*(D+1))*monomialWorkingWidth D W

theorem cacheWidthPlan_valid : ∀a∈cacheWidthPlan,a.Valid cacheDimensionIds := by
  simp [cacheWidthPlan,NatAssign.Instruction.Valid,cacheDimensionIds]
theorem cacheAddressPlan_valid : ∀a∈cacheAddressPlan,a.Valid cacheDimensionIds := by
  simp [cacheAddressPlan,NatAssign.Instruction.Valid,cacheDimensionIds]

theorem cacheWidthValues_eq (D W heap i : ℕ) : cacheWidthValues D W heap i=
    if i=723 then monomialWorkingWidth D W else if i=724 then 4*(D+1)
    else if i=728 then 4 else cacheDimensionInput D W heap i := by
  by_cases h : i∈({723,724,728}:Finset ℕ)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl <;>
      simp [cacheWidthValues,cacheWidthPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,cacheDimensionInput,
        monomialWorkingWidth,monomialStorageWidth] <;> ring
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [cacheWidthValues,values_unchanged cacheWidthPlan _ i (by
      simp [cacheWidthPlan,NatAssign.Instruction.target];omega)]
    simp [h.1,h.2.1,h.2.2]

theorem cacheDimensionValues_eq (D W heap i : ℕ) : cacheDimensionValues D W heap i=
    if i=725 then 4*(D+1) else if i=726 then monomialWorkingWidth D W
    else if i=727 then heap else if i=728 then 3 else if i=729 then cacheNextBase D W heap
    else cacheWidthValues D W heap i := by
  by_cases h : i∈({725,726,727,728,729}:Finset ℕ)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;>
      simp [cacheDimensionValues,cacheAddressPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,cacheWidthValues_eq,
        cacheDimensionInput,cacheNextBase]
    all_goals ring
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [cacheDimensionValues,values_unchanged cacheAddressPlan _ i (by
      simp [cacheAddressPlan,NatAssign.Instruction.target];omega)]
    simp [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2]

def cacheDimensionCode : Code := .seq (NatAssign.code cacheWidthPlan) (NatAssign.code cacheAddressPlan)
def cacheDimensionBound (B : ℕ) : ℕ := 2^32*(B+1)
def cacheDimensionCost (B : ℕ) : ℕ := stageCost B+stageCost (2^22*(B+1))

theorem cacheDimensionInput_width (D W heap B i : ℕ)
    (hD : D.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B) :
    (cacheDimensionInput D W heap i).bits.length≤B := by
  unfold cacheDimensionInput
  split_ifs <;> first | exact hD | exact hW | exact hh | simp

theorem cacheWidthPlan_literalWidth (B : ℕ) (hB : 5≤B) :
    ∀a∈cacheWidthPlan,a.literalWidth≤B := by
  simp [cacheWidthPlan,NatAssign.Instruction.literalWidth,
    show (2:ℕ).bits.length=2 from rfl,show (3:ℕ).bits.length=2 from rfl,
    show (8:ℕ).bits.length=4 from rfl,show (17:ℕ).bits.length=5 from rfl,
    show (16:ℕ).bits.length=5 from rfl,
    show (4:ℕ).bits.length=3 from rfl]
  omega

theorem cacheWidthValues_width (D W heap B : ℕ) (hB : 5≤B)
    (hD : D.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B)
    (i : ℕ) (hi : i∈cacheDimensionIds) :
    (cacheWidthValues D W heap i).bits.length≤2^22*(B+1) := by
  have h := NatAssign.values_width_bound cacheDimensionIds cacheWidthPlan cacheWidthPlan_valid
    (cacheDimensionInput D W heap) B (fun i _ => cacheDimensionInput_width D W heap B i hD hW hh)
    (cacheWidthPlan_literalWidth B hB) i hi
  change (cacheWidthValues D W heap i).bits.length+1≤2^21*(B+1) at h
  omega

theorem cacheDimensionValues_width (D W heap B : ℕ) (hB : 5≤B)
    (hD : D.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B)
    (i : ℕ) (hi : i∈cacheDimensionIds) :
    (cacheDimensionValues D W heap i).bits.length≤cacheDimensionBound B := by
  have h := NatAssign.values_width_bound cacheDimensionIds cacheAddressPlan cacheAddressPlan_valid
    (cacheWidthValues D W heap) (2^22*(B+1))
    (cacheWidthValues_width D W heap B hB hD hW hh)
    (by simp [cacheAddressPlan,NatAssign.Instruction.literalWidth,
      show (3:ℕ).bits.length=2 from rfl];omega) i hi
  change (cacheDimensionValues D W heap i).bits.length+1≤2^8*(2^22*(B+1)+1) at h
  unfold cacheDimensionBound
  omega

theorem cacheDimension_executes (D W heap B : ℕ) (hB : 5≤B)
    (hD : D.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank cacheDimensionIds (cacheDimensionInput D W heap) s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape cacheDimensionCode cost s t ∧ cost≤cacheDimensionCost B ∧
      NatAssign.Bank cacheDimensionIds (cacheDimensionValues D W heap) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame ({0,1,2,3}∪cacheDimensionIds) s.val t.val := by
  have ge (i : ℕ) (hi : i∈cacheDimensionIds) : 4 ≤ i := by
    simp only [cacheDimensionIds,Finset.mem_Icc] at hi;omega
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := fixedBankStage_executes cacheDimensionIds ge
    cacheWidthPlan cacheWidthPlan_valid (by decide) (cacheDimensionInput D W heap) B
    (fun i _ => cacheDimensionInput_width D W heap B i hD hW hh)
    (cacheWidthPlan_literalWidth B hB) input tape s hs hz
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := fixedBankStage_executes cacheDimensionIds ge
    cacheAddressPlan cacheAddressPlan_valid (by decide) (cacheWidthValues D W heap) (2^22*(B+1))
    (cacheWidthValues_width D W heap B hB hD hW hh)
    (by simp [cacheAddressPlan,NatAssign.Instruction.literalWidth,
      show (3:ℕ).bits.length=2 from rfl];omega) input tape s0 b0 z0
  exact ⟨c0+c1,t,e0.seq e1,by unfold cacheDimensionCost;omega,b1,z1,f0.trans f1⟩

theorem cacheDimensionCost_polynomial (B : ℕ) : cacheDimensionCost B≤2^144*(B+2)^2 := by
  have h : stageCost (2^22*(B+1))≤2^142*(B+2)^2 := by
    unfold stageCost
    calc
      _≤2^96*(2^23*(B+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  change 2^96*(B+2)^2+stageCost (2^22*(B+1))≤_
  omega

#print axioms cacheDimension_executes
#print axioms cacheDimensionCost_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
