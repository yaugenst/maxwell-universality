import Maxwell.Continuum.NaturalBankStage
import Maxwell.Continuum.RationalDataflowArray

/-! Lift a checked natural-word stage to its rational-bank interpretation.
This bridge is independent of a fixed bank size or physical application. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem naturalStage_parts (S allIds : Finset ℕ) (hparts : ids S⊆allIds)
    (hIds : ∀k∈allIds,10≤k) (plan : List NatAssign.Instruction)
    (valid : ∀a∈plan,a.Valid allIds) (length : plan.length≤25)
    (n : ℕ → ℕ) (v : ℕ → Parts) (B : ℕ)
    (width : ∀k∈allIds,(n k).bits.length≤B) (literals : ∀a∈plan,a.literalWidth≤B)
    (agree : ∀k∈ids S,NatAssign.values plan n k=dataValues v k)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (scratch : NatAssign.Scratch s.val) (four : RationalAccumulator.Blank s.val 4) :
    ∃cost t,Executes input tape (NatAssign.code plan) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank allIds (NatAssign.values plan n) t.val ∧ Ready S v t ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame ({0,1,2,3,4}∪allIds) s.val t.val := by
  obtain ⟨cost,t,e,hc,bank,blank,frame⟩ := fixedBankStage_executes allIds
    (fun k hk => by have := hIds k hk;omega) plan valid length n B width literals input tape s hs scratch
  have ready : Ready S v t := ⟨fun k hk => by
    simpa only [agree k hk] using bank k (hparts hk),blank⟩
  have allBlank (k : ℕ) (hk : k<5) : RationalAccumulator.Blank t.val k := by
    by_cases h4 : k<4
    · exact blank k h4
    · have he : k=4 := by omega
      subst k
      have outside : 4∉allIds := fun h => by have := hIds 4 h;omega
      exact RationalAccumulator.blank_of_eq (frame.tapes 4 (by simp [outside])) four
  exact ⟨cost,t,e,hc,bank,ready,allBlank,frame.mono (by
    intro k hk
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto)⟩

#print axioms naturalStage_parts
end Maxwell.Continuum.RationalDataflow
