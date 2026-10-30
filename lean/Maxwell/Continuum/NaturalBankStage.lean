import Maxwell.Continuum.RationalDataflowExecution

/-! Fixed natural-word arithmetic with an explicit arbitrary register bank. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

theorem fixedBankStage_executes (allIds : Finset ℕ) (hids : ∀ i∈allIds, 4 ≤ i)
    (ins : List NatAssign.Instruction) (hv : ∀ a∈ins, a.Valid allIds) (hl : ins.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀ i∈allIds, (v i).bits.length≤B)
    (hc : ∀ a∈ins, a.literalWidth≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code ins) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank allIds (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪allIds) s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hf⟩ := NatAssign.executes allIds hids ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound allIds ins hv v B hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^96 := by
    calc
      _ ≤ 3000*8^25 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  refine ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',hf.mono ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ hi
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    apply Finset.mem_union_right
    have hh := hv a ha
    cases a <;> first | exact hh | exact hh.2.1

#print axioms fixedBankStage_executes
end Maxwell.Continuum.RationalDataflow
