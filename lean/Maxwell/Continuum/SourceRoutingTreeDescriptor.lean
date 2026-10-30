import Maxwell.Continuum.SourceRoutingTreeDescriptorPlan

/-! One fixed runtime descriptor program computes the five node inputs,
including both child-permutation addresses, before each split visit. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Descriptor
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem executes (v : ℕ→ℕ) (htwo : v 819=2)
    (hzero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (B : ℕ) (hB : 3 ≤ B) (hw : ∀i∈Division.ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ 2^160*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ BinaryPrecision.Frame Division.work s.val t.val := by
  have prepare_lit : ∀a∈prepare,a.literalWidth ≤ B := by
    simp [prepare,NatAssign.Instruction.literalWidth]
  obtain ⟨c0,a,e0,h0,b0,z0,f0⟩ := Arithmetic.stage prepare prepare_valid v B hw prepare_lit input tape s hs hc
  have w0 : ∀i∈Division.ids,(NatAssign.values prepare v i).bits.length ≤ 4*(B+1) := by
    intro i hi
    have hh := NatAssign.values_width_bound Division.ids prepare prepare_valid v B hw prepare_lit i hi
    change _+1 ≤ 4*(B+1) at hh
    omega
  have az : Blank a.val 839 := RationalAccumulator.blank_of_eq (f0.tapes 839 (by decide)) h839
  have hzero0 : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      NatAssign.values prepare v i=0 := by
    intro i hi
    rw [prepare_other v i (by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega)]
    exact hzero i hi
  have atwo : NatAssign.values prepare v 819=2 := (prepare_other v 819 (by decide)).trans htwo
  obtain ⟨c1,b,e1,h1,b1,z1,bz,f1⟩ := Division.executes 805 819 816 817 (by decide) (by decide)
    (by decide) (by decide) (by decide) (NatAssign.values prepare v) hzero0 (by rw [atwo];decide)
    (4*(B+1)) w0 input tape a b0 z0 az
  rw [divided_eq v htwo] at b1
  have w1 : ∀i∈Division.ids,(divided v i).bits.length ≤ 4*(B+1) := by
    intro i hi
    by_cases hq : i=816
    · subst i
      have hh := (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v 814+v 815) 2)).trans
        (by simpa only [prepare_value] using w0 805 (by decide))
      simpa only [divided,Function.update_self,Function.update_of_ne (by decide : (816 : ℕ)≠817)] using hh
    · by_cases hr : i=817
      · subst i
        have hh := (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v 814+v 815) 2)).trans
          (by simpa only [prepare_value] using w0 805 (by decide))
        simpa only [divided,Function.update_self] using hh
      · simpa only [divided,Function.update_of_ne hq,Function.update_of_ne hr] using w0 i hi
  have finish_lit : ∀a∈finish,a.literalWidth ≤ 4*(B+1) := by
    simp only [finish,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,
      show (6 : ℕ).bits.length=3 by decide]
    all_goals omega
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := Arithmetic.stage finish finish_valid (divided v) (4*(B+1)) w1
    finish_lit input tape b b1 z1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide)) bz,
    (f0.mono Arithmetic.work_subset).trans (f1.trans (f2.mono Arithmetic.work_subset))⟩
  change c0 ≤ 3000*8^2*(B+2)^2 at h0
  change c2 ≤ 3000*8^24*(4*(B+1)+2)^2 at h2
  have hsq : (4*(B+1)+2)^2 ≤ 16*(B+2)^2 := by nlinarith
  have hunit : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
  calc
    _ ≤ (3000*8^2+16*2^100+16*(3000*8^24)+1)*(B+2)^2 := by
      nlinarith only [h0,h1,h2,hsq,hunit]
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Descriptor
