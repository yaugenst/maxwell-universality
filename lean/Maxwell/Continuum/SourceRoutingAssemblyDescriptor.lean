import Maxwell.Continuum.SourceRoutingAssemblyDescriptorPlan

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyDescriptor
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem divided_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(divided v i).bits.length ≤ B := by
  intro i hi
  by_cases h817 : i=817
  · subst i
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v 812) (v 819))).trans (hw 812 (by decide))
  · by_cases h816 : i=816
    · subst i
      exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v 812) (v 819))).trans (hw 812 (by decide))
    · simpa only [divided,Function.update_of_ne h817,Function.update_of_ne h816] using hw i hi

theorem finish_literals (B : ℕ) (hB : 4 ≤ B) : ∀a∈finish,a.literalWidth ≤ B := by
  simp only [finish,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [NatAssign.Instruction.literalWidth,
    show (10 : ℕ).bits.length=4 by decide,show (2 : ℕ).bits.length=2 by decide]
  all_goals omega

def wordBound (B : ℕ) : ℕ := 2^35*(B+1)

theorem output_word_width (v : ℕ→ℕ) (B : ℕ) (hB : 4 ≤ B)
    (hw : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(output v i).bits.length ≤ wordBound B := by
  intro i hi
  have hh:=NatAssign.values_width_bound Division.ids finish finish_valid (divided v) B
    (divided_width v B hw) (finish_literals B hB) i hi
  exact (Nat.le_add_right _ 1).trans hh

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 4 ≤ B) (htwo : v 819=2)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hw : ∀i∈Division.ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^120*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=Division.executes 812 819 816 817
    (by decide) (by decide) (by decide) (by decide) (by decide) v hz (by omega) B hw input tape s hs hc h839
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩:=Arithmetic.stage finish finish_valid (divided v) B
    (divided_width v B hw) (finish_literals B hB) input tape a b0 z0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,
    RationalAccumulator.blank_of_eq (f1.tapes 839 (by decide)) a839,
    f0.trans (f1.mono Arithmetic.work_subset)⟩
  change c1 ≤ 3000*8^35*(B+2)^2 at h1
  have unit : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
  nlinarith only [h0,h1,unit]

#print axioms executes
#print axioms output_word_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyDescriptor
