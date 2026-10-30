import Maxwell.Continuum.SourceRoutingAssemblySetupPlan

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem setup_workspace {s t : BitRAMState} (hs : DoublingInit.Workspace s)
    (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame (NatAssign.changes setup) s t) :
    DoublingInit.Workspace t := by
  have keep (i : ℕ) (hi : i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=37 ∨ (88 ≤ i ∧ i ≤ 92)) :
      t.tapes i=s.tapes i := by
    apply hf.tapes
    have he : NatAssign.changes setup=({0,1,2,3,80,100,122,124,85,86,96}:Finset ℕ) := by decide
    rw [he]
    simp only [Finset.mem_insert,Finset.mem_singleton];omega
  refine ⟨⟨⟨hz 0 (by omega),hz 1 (by omega),hz 2 (by omega),hz 3 (by omega),
    ?_,?_,?_,?_⟩,?_,?_⟩,?_⟩
  · exact RationalAccumulator.blank_of_eq (keep 5 (by omega)) hs.1.1.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 6 (by omega)) hs.1.1.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 8 (by omega)) hs.1.1.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 9 (by omega)) hs.1.1.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (keep 7 (by omega)) hs.1.2.1
  · intro i hi;exact RationalAccumulator.blank_of_eq (keep i (by dsimp only [DoublingPass.Private] at hi;omega)) (hs.1.2.2 i hi)
  · exact RationalAccumulator.blank_of_eq (keep 37 (by omega)) hs.2

theorem setup_executes (q : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hq : ∀i∈controls,(q i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NodeVisit.Clean s.val)
    (hi : ∀i∈controls,RationalAccumulator.Word s.val i (q i)) :
    ∃steps t, Executes input tape setupCode steps s t ∧ steps ≤ 2^40*(B+2)^2 ∧
      NatAssign.Bank ids (setupValues q) t.val ∧ DoublingInit.Workspace t.val ∧
      BinaryPrecision.Frame setupWork s.val t.val := by
  have scratch : NatAssign.Scratch s.val := by
    intro i hi
    apply (Workspace.raw_iff s.val).mp hs i
    exact Finset.mem_union_left _ (by simp only [Workspace.small,Finset.mem_insert,Finset.mem_singleton];omega)
  have lower : ∀i∈ids,4 ≤ i := by
    intro i hi
    simp only [ids,controls,NodeCleanup.banks,Finset.mem_union,Finset.mem_Icc,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  have width : ∀i∈ids,(initial q i).bits.length ≤ B := by
    intro i _
    by_cases hc : i∈controls
    · simpa [initial,hc] using hq i hc
    · simp [initial,hc]
  have literal : ∀a∈setup,a.literalWidth ≤ B := by
    simp [setup,NatAssign.Instruction.literalWidth];omega
  obtain ⟨c,a,ea,hc,ba,za,fa⟩:=NatAssign.executes ids lower setup setup_valid (initial q)
    input tape s (initial_bank q s.val hs hi) scratch
  have source : RationalAccumulator.Word a.val 801 (q 801) := by
    simpa [setup,initial,controls,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      Function.update] using ba 801 (by decide)
  obtain ⟨so,hso⟩:=source
  obtain ⟨co,hco⟩:=RationalAccumulator.blank_of_eq (fa.tapes 83 (by decide)) (hs.2 83 (by decide))
  obtain ⟨t,ec,tt,tf⟩:=WordCall.clone 801 83 (by decide) input tape (q 801).bits so co a hso hco
  have cf : BinaryPrecision.Frame {83} a.val t.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠83 by simpa using hi)]
  have bt : NatAssign.Bank ids (setupValues q) t.val := by
    intro i hi
    by_cases he : i=83
    · subst i
      exact ⟨co,by simp only [setupValues,Function.update_self,tt]⟩
    · simpa only [setupValues,Function.update_of_ne he] using
        RationalAccumulator.word_of_eq (cf.tapes i (by simpa using he)) (ba i hi)
  have work : DoublingInit.Workspace t.val := by
    apply DoublingInit.workspace_of_tapes (s:=a.val) (w:=setup_workspace hs.1 za fa)
    intro i hi
    apply cf.tapes
    simp only [Finset.mem_singleton]
    rcases hi with hi|hi
    · omega
    · simp only [DoublingInit.Private,DoublingPass.Private] at hi;omega
  refine ⟨c+(15*(q 801).bits.length+17),t,ea.seq ec,?_,bt,work,
    (fa.mono Finset.subset_union_left).trans (cf.mono Finset.subset_union_right)⟩
  have price:=NatAssign.price_bound ids setup setup_valid (initial q) B width literal
  change NatAssign.price setup (initial q) ≤ 3000*8^7*(B+2)^2 at price
  have hcount:=hq 801 (by decide)
  have linear : 15*B+17 ≤ 17*(B+2)^2 := by nlinarith
  nlinarith only [hc,price,hcount,linear]

#print axioms setup_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
