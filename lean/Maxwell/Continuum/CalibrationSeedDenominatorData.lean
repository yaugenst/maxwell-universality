import Maxwell.Continuum.CalibrationSeedRadicalMachine
import Maxwell.Continuum.CalibrationSeedScalarParts
import Maxwell.Cost.Structured.NatAssign.Difference

/-! Exact natural operations preparing the second seed square root. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def denominatorPrepare : List NatAssign.Instruction :=
  [.copy 32 702,.copy 548 703,.copy 544 712,
   .literal 704 8,.literal 705 361,.literal 706 28,.literal 707 225,
   .copy 703 708,.multiply 705 708,.multiply 704 708,
   .copy 702 709,.multiply 706 709,.multiply 704 709,
   .copy 703 710,.multiply 707 710,.literal 711 0]
def denominatorPrepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values denominatorPrepare v
def denominatorDifference (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (denominatorPrepared v) 711 (denominatorNumerator (v 32) (v 548))
def denominatorClear : List ℕ := (List.range 549).filter (fun i=>i∈RationalRoot.Raw.ids\{228,229,544})
def denominatorLoad : List NatAssign.Instruction :=
  denominatorClear.map (fun i=>.literal i 0)++[.copy 711 228,.copy 710 229,.copy 712 544]
def denominatorLoaded (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values denominatorLoad (denominatorDifference v)
def componentIds : Finset ℕ := {32,548}∪savedIds
def denominatorValues (v : ℕ→ℕ) (num den : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (denominatorLoaded v) 32 num) 548 den

theorem denominatorPrepare_valid : ∀a∈denominatorPrepare,a.Valid ids := by
  simp [denominatorPrepare,NatAssign.Instruction.Valid,ids,savedIds,RationalRoot.Raw.ids,
    RationalRoot.ids,NaturalRoot.fullIds]
theorem denominatorLoad_valid : ∀a∈denominatorLoad,a.Valid ids := by
  intro a ha
  simp only [denominatorLoad,List.mem_append] at ha
  rcases ha with first|rest
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp first
    have member : i∈RationalRoot.Raw.ids := by
      have h := (List.mem_filter.mp hi).2
      exact (Finset.mem_sdiff.mp (of_decide_eq_true h)).1
    exact Finset.mem_union_left _ member
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at rest
    rcases rest with rfl|rfl|rfl <;>
      simp [NatAssign.Instruction.Valid,ids,savedIds,RationalRoot.Raw.ids,
        RationalRoot.ids,RationalCanonicalBank.ids]
theorem componentIds_subset : componentIds⊆ids := by decide+kernel

theorem denominatorPrepared_fields (v : ℕ→ℕ) :
    denominatorPrepared v 708=denominatorPositive (v 548) ∧
    denominatorPrepared v 709=denominatorNegative (v 32) ∧
    denominatorPrepared v 710=denominatorBase (v 548) ∧ denominatorPrepared v 711=0 ∧
    denominatorPrepared v 702=v 32 ∧ denominatorPrepared v 703=v 548 ∧
    denominatorPrepared v 712=v 544 := by
  simp [denominatorPrepared,denominatorPrepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,denominatorPositive,denominatorNegative,
    denominatorBase]
  constructor <;> ring

theorem denominatorLoaded_root (v : ℕ→ℕ) (i : ℕ) (hi : i∈RationalRoot.Raw.ids) :
    denominatorLoaded v i=RationalRoot.Raw.inputValues
      (denominatorNumerator (v 32) (v 548)) (denominatorBase (v 548)) (v 544) i := by
  have keep : i≠711 ∧ i≠710 ∧ i≠712 := by
    have bound : ∀i∈RationalRoot.Raw.ids,i<600 := by decide+kernel
    have := bound i hi
    omega
  have notClear (j : ℕ) (hj : 700 ≤ j) : j∉denominatorClear := by
    have bound : ∀i∈denominatorClear,i<600 := by decide+kernel
    intro member;have :=bound j member;omega
  simp only [denominatorLoaded,denominatorLoad,NatAssign.values_append,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  simp only [NatAssign.values_literals,ite_eq_right (notClear 711 (by decide)),
    ite_eq_right (notClear 710 (by decide)),ite_eq_right (notClear 712 (by decide)),
    denominatorDifference,Function.update_self,Function.update_of_ne (by decide : 710≠711),
    Function.update_of_ne (by decide : 712≠711),
    Function.update_of_ne (by decide : 710≠228),Function.update_of_ne (by decide : 712≠228),
    Function.update_of_ne (by decide : 712≠229),
    (denominatorPrepared_fields v).2.2.1,(denominatorPrepared_fields v).2.2.2.2.2.2]
  by_cases a : i=544
  · subst i;simp [RationalRoot.Raw.inputValues]
  by_cases b : i=228
  · subst i;simp [a,RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]
  by_cases c : i=229
  · subst i;simp [a,b,RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]
  have clear : i∈denominatorClear := by
    have bound : ∀j∈RationalRoot.Raw.ids,j<549 := by decide+kernel
    simp [denominatorClear,hi,a,b,c,bound i hi]
  simp [a,b,c,NatAssign.values_literals,clear,RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]

theorem denominatorValues_fields (v : ℕ→ℕ) (num den : ℕ) :
    denominatorValues v num den 32=num ∧ denominatorValues v num den 548=den ∧
    denominatorValues v num den 702=v 32 ∧ denominatorValues v num den 703=v 548 ∧
    denominatorValues v num den 712=v 544 := by
  have keep (i : ℕ) (hi : i∈({702,703,712}:Finset ℕ)) : denominatorLoaded v i=denominatorPrepared v i := by
    rw [denominatorLoaded,NatAssign.values_preserves denominatorLoad _ i (by
      have all : ∀i∈({702,703,712}:Finset ℕ),∀a∈denominatorLoad,i≠a.target := by decide+kernel
      exact all i hi)]
    apply Function.update_of_ne
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  simp [denominatorValues,keep 702 (by decide),keep 703 (by decide),keep 712 (by decide),
    (denominatorPrepared_fields v).2.2.2.2.1,(denominatorPrepared_fields v).2.2.2.2.2.1,
    (denominatorPrepared_fields v).2.2.2.2.2.2]

#print axioms denominatorLoaded_root
end Maxwell.Continuum.Calibration.SeedMachine
