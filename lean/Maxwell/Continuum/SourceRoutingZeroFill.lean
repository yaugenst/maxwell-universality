import Maxwell.Continuum.SourceRoutingZeroSetup

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem fill_executes (q : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hq : ∀i∈controls,(q i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NodeVisit.Clean s.val) (hb : NatAssign.Bank ids (output q) s.val) :
    ∃steps t,Executes input tape (PositiveGraph.Initialize.fillCode ports) steps s t ∧
      steps ≤ PositiveGraph.Initialize.fillCost (q 801) B ∧ NodeVisit.Clean t.val ∧
      NatAssign.Bank ids (output q) t.val ∧
      (∀p,q 800 ≤ p→p<q 800+q 801→t.val.memory p=false) ∧
      PositiveGraph.Initialize.Outside (q 800) 1 (q 801) s.val t.val ∧
      PositiveGraph.Initialize.Frame s.val t.val := by
  have small : (1 : ℕ).bits.length=1 := by decide
  have ready : PositiveGraph.Initialize.Ready ports (1 : ℕ).bits (q 800).bits (1 : ℕ).bits 0 s.val :=
    ⟨hs.1.1.1,hs.1.1.2.1,hs.1.2,hb 140 (by decide),hb 141 (by decide),hb 140 (by decide),hb 162 (by decide)⟩
  have h160 : Blank s.val 160 := (RationalAccumulator.zero_word_iff_blank _ _).mp (hb 160 (by decide))
  have h161 : Blank s.val 161 := (RationalAccumulator.zero_word_iff_blank _ _).mp (hb 161 (by decide))
  have size : q 801<2^B := by
    apply Nat.size_le.mp
    simpa only [Nat.size_eq_bits_len] using hq 801 (by decide)
  obtain ⟨steps,t,hcost,he,rt,z160,z161,rep,outside,frame⟩:=PositiveGraph.Initialize.fill_executes
    ports (1 : ℕ).bits (q 800).bits (1 : ℕ).bits (q 801) 0 B
    (by omega) (hq 800 (by decide)) (hq 801 (by decide)) (by omega)
    (by rw [addressValue_bits];decide) (by simpa only [addressValue_bits] using hB)
    (by rw [addressValue_bits];exact small) (by rw [addressValue_bits];decide) size input tape s ready h160 h161
    (hb 142 (by decide))
  have clean : NodeVisit.Clean t.val := by
    refine ⟨⟨⟨rt.scratch,rt.seven,?_⟩,rt.temporary⟩,?_⟩
    · intro i hi
      exact RationalAccumulator.blank_of_eq (frame.tapes i (by dsimp only [DoublingPass.Private] at hi;omega)
        (by dsimp only [DoublingPass.Private] at hi;omega) (by dsimp only [DoublingPass.Private] at hi;omega)
        (by dsimp only [DoublingPass.Private] at hi;omega) (by dsimp only [DoublingPass.Private] at hi;omega))
        (hs.1.1.2.2 i hi)
    · intro i hi
      apply RationalAccumulator.blank_of_eq (frame.tapes i ?_ ?_ ?_ ?_ ?_) (hs.2 i hi)
      all_goals simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false] at hi
      all_goals omega
  have bank : NatAssign.Bank ids (output q) t.val := by
    intro i hi
    by_cases h160 : i=160
    · subst i;exact (RationalAccumulator.zero_word_iff_blank _ _).mpr z160
    · by_cases h161 : i=161
      · subst i;exact (RationalAccumulator.zero_word_iff_blank _ _).mpr z161
      · by_cases h162 : i=162
        · subst i;exact rt.valueWord
        · apply RationalAccumulator.word_of_eq (frame.tapes i ?_ ?_ h160 h161 h162) (hb i hi)
          all_goals simp only [ids,controls,banks,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
          all_goals omega
  refine ⟨steps,t,he,hcost,clean,bank,?_,?_,frame⟩
  · intro p hlo hhi
    have hh:=rep.bits ⟨p-q 800,by omega⟩ 0 (by rw [addressValue_bits];decide)
    simp only [addressValue_bits,Nat.mul_one,Nat.add_zero] at hh
    rw [show q 800+(p-q 800)=p by omega] at hh
    simpa [Vector.get,Fin.cast,show FixedWidth.bits 1 []=[false] by decide] using hh
  · simpa only [addressValue_bits] using outside

#print axioms fill_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
