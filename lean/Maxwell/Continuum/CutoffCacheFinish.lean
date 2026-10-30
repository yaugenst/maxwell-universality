import Maxwell.Continuum.CutoffCacheNaturalBank
import Maxwell.Continuum.CutoffCacheBoundary

/-! The actual second-buffer endpoint is written to the shared heap cursor;
all ten temporary cache descriptor words are then erased by charged code. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def cacheFinishIds : Finset ℕ := insert 709 cacheDimensionIds
def cacheFinishInput (D W H : ℕ) (i : ℕ) : ℕ :=
  if i=709 then H else Profile.Runtime.cacheNaturalValues D W H i

def cacheFinishPlan : List NatAssign.Instruction :=
  [.copy 728 723,.literal 724 3,.multiply 724 723,.copy 729 709,.add 723 709,
   .literal 720 0,.literal 721 0,.literal 722 0,.literal 723 0,.literal 724 0,
   .literal 725 0,.literal 726 0,.literal 727 0,.literal 728 0,.literal 729 0]
def cacheFinishCode : Code := NatAssign.code cacheFinishPlan

theorem cacheFinishPlan_valid : ∀a∈cacheFinishPlan,a.Valid cacheFinishIds := by
  simp [cacheFinishPlan,NatAssign.Instruction.Valid,cacheFinishIds,cacheDimensionIds]

theorem cacheFinishValues_eq (D W H i : ℕ) (hi : i∈cacheFinishIds) :
    NatAssign.values cacheFinishPlan (cacheFinishInput D W H) i=
      if i=709 then cacheEndBase D W H else 0 := by
  simp only [cacheFinishIds,cacheDimensionIds,Finset.mem_insert,Finset.mem_Icc] at hi
  rcases hi with rfl|⟨hlo,hhi⟩
  · simp [cacheFinishPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,cacheFinishInput,
      Profile.Runtime.cacheNaturalValues,cacheEndBase,cacheNextBase]
    ring
  · interval_cases i <;> simp [cacheFinishPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem cacheFinishInput_width (D W H : ℕ) (hh : H.bits.length≤W)
    (i : ℕ) (hi : i∈cacheFinishIds) :
    (cacheFinishInput D W H i).bits.length≤2*monomialWorkingWidth D W+3 := by
  have hbits := cache_header_bound D W H hh
  have hD := cache_nat_bits_le D
  have hW := cache_nat_bits_le W
  have hB := cache_nat_bits_le (monomialWorkingWidth D W)
  have hprod := RationalAccumulator.bits_mul_le (4*(D+1)) (monomialWorkingWidth D W)
  have dw : D+W≤monomialWorkingWidth D W := by
    unfold monomialWorkingWidth monomialStorageWidth
    omega
  simp only [cacheFinishIds,cacheDimensionIds,Finset.mem_insert,Finset.mem_Icc] at hi
  rcases hi with rfl|⟨hlo,hhi⟩
  · simp only [cacheFinishInput,ite_true]
    omega
  · interval_cases i <;> simp [cacheFinishInput,Profile.Runtime.cacheNaturalValues] <;> omega

theorem cacheFinish_executes (D W H : ℕ) (hh : H.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hn : NatAssign.Bank cacheDimensionIds (Profile.Runtime.cacheNaturalValues D W H) s.val)
    (heap : RationalAccumulator.Word s.val 709 H) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape cacheFinishCode cost s t ∧
      cost≤2^104*(monomialWorkingWidth D W+8)^2 ∧
      RationalAccumulator.Word t.val 709 (cacheEndBase D W H) ∧
      (∀i∈cacheDimensionIds,Blank t.val i) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪cacheFinishIds) s.val t.val := by
  have bank : NatAssign.Bank cacheFinishIds (cacheFinishInput D W H) s.val := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact heap
    · simpa only [cacheFinishInput,ite_eq_right (show i≠709 by
        simp only [cacheDimensionIds,Finset.mem_Icc] at hi;omega)] using hn i hi
  obtain ⟨cost,t,ex,hcost,bt,zt,ft⟩ := fixedBankStage_executes cacheFinishIds (by
    intro i hi
    simp only [cacheFinishIds,cacheDimensionIds,Finset.mem_insert,Finset.mem_Icc] at hi
    omega) cacheFinishPlan cacheFinishPlan_valid (by decide) (cacheFinishInput D W H)
      (2*monomialWorkingWidth D W+3) (cacheFinishInput_width D W H hh)
      (by simp [cacheFinishPlan,NatAssign.Instruction.literalWidth,
        show (3:ℕ).bits.length=2 from rfl]) input tape s bank hz
  refine ⟨cost,t,ex,hcost.trans ?_,?_,?_,zt,ft⟩
  · unfold stageCost
    have h := Nat.pow_le_pow_left (show 2*monomialWorkingWidth D W+3+2≤
      4*(monomialWorkingWidth D W+8) by omega) 2
    nlinarith only [h]
  · simpa only [cacheFinishValues_eq D W H 709 (by decide),ite_true] using bt 709 (by decide)
  · intro i hi
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    have he : i≠709 := by simp only [cacheDimensionIds,Finset.mem_Icc] at hi;omega
    simpa only [cacheFinishValues_eq D W H i (Finset.mem_insert_of_mem hi),ite_eq_right he] using
      bt i (Finset.mem_insert_of_mem hi)

#print axioms cacheFinish_executes
end Maxwell.Continuum.Calibration.RawCutoff
