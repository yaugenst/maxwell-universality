import Maxwell.Continuum.SourceRoutingAssemblySetup

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

structure State (q : ℕ→ℕ) (k : ℕ) (clock childClock : List Bool) (s : BitRAMState) : Prop where
  config : ChildPermutation.Config (layout q) [] clock childClock s
  workspace : DoublingInit.Workspace s
  count : Word s 96 (2*2^k).bits
  childCount : Word s 127 (2^k).bits
  colorSource : Word s 85 (q 805).bits
  zero126 : Blank s 126
  unused : ∀i∈NodeCleanup.banks,i∉live→Blank s i

theorem prepared (q : ℕ→ℕ) (k : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (setupValues q) s.val) (hs : DoublingInit.Workspace s.val) :
    ∃steps t childClock,Executes input tape ChildPermutation.prepareCode steps s t ∧
      steps ≤ ChildPermutation.prepareCost (layout q) k (q 801).bits ∧
      State q k (q 801).bits childClock t.val ∧ childClock.length=(layout q).childWidth ∧
      ChildPermutation.MetadataFrame s.val t.val := by
  have count : Word s.val 96 (2*2^k).bits := by
    have h : RationalAccumulator.Word s.val 96 (q 801) := hb 96 (by decide)
    simpa only [RationalAccumulator.Word,BankArray.Word,hn] using h
  have blank (i : ℕ) (hi : i∈({120,121,127,128,87,126}:Finset ℕ)) : Blank s.val i := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    all_goals exact hb _ (by decide)
  obtain ⟨steps,t,cc,hcost,he,cfg,hcc,child,work,frame⟩:=ChildPermutation.prepare_executes k input tape
    (layout q) (q 801).bits hw (by simpa only [layout,hw] using NodeSetup.clock_length q k hn)
    s (setup_before q s.val hb) hs count (blank 120 (by decide)) (blank 121 (by decide))
    (blank 127 (by decide)) (blank 128 (by decide)) (blank 87 (by decide))
  refine ⟨steps,t,cc,he,hcost,⟨cfg,work,?_,child,?_,?_,?_⟩,hcc,frame⟩
  · exact BankArray.word_of_eq (frame.2.2.2.2.1 96 (by simp [ChildPermutation.MetadataPrivate])) count
  · have h : Word s.val 85 (q 805).bits := hb 85 (by decide)
    exact BankArray.word_of_eq (frame.2.2.2.2.1 85 (by simp [ChildPermutation.MetadataPrivate])) h
  · exact RationalAccumulator.blank_of_eq (frame.2.2.2.2.1 126 (by simp [ChildPermutation.MetadataPrivate])) (blank 126 (by decide))
  · intro i hi hl
    have wi:=hb i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
    rw [setup_unwritten q i hi hl] at wi
    apply RationalAccumulator.blank_of_eq (frame.2.2.2.2.1 i ?_) ((RationalAccumulator.zero_word_iff_blank _ _).mp wi)
    simp only [ChildPermutation.MetadataPrivate]
    intro hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals exact hl (by decide)

theorem State.pass {q : ℕ→ℕ} {k : ℕ} {clock childClock : List Bool} {s t : BitRAMState}
    (hs : State q k clock childClock s)
    (cfg : ChildPermutation.Config (layout q) [] clock childClock t)
    (work : DoublingInit.Workspace t) (zero126 : Blank t 126)
    (frame : ChildPermutation.LoopFrame s t) : State q k clock childClock t := by
  have keep (i : ℕ) (hi : i=96 ∨ i=127 ∨ i=85) : t.tapes i=s.tapes i := by
    apply frame.2.2.2.1 i (by omega) (by omega) (by omega)
    simp only [ChildPermutation.Private,DoublingInit.Private,DoublingPass.Private];omega
  refine ⟨cfg,work,BankArray.word_of_eq (keep 96 (by omega)) hs.count,
    BankArray.word_of_eq (keep 127 (by omega)) hs.childCount,
    BankArray.word_of_eq (keep 85 (by omega)) hs.colorSource,zero126,?_⟩
  intro i hi hl
  by_cases hp : DoublingPass.Private i
  · exact work.1.2.2 i hp
  · apply RationalAccumulator.blank_of_eq (frame.2.2.2.1 i ?_ ?_ ?_ ?_) (hs.unused i hi hl)
    · simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false] at hi;omega
    · intro he;subst i;exact hl (by decide)
    · intro he;subst i;exact hl (by decide)
    · simp only [ChildPermutation.Private,DoublingInit.Private]
      intro h
      rcases h with rfl|h
      · simp [NodeCleanup.banks] at hi
      · exact hp h

#print axioms prepared
#print axioms State.pass
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
