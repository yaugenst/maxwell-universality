import Maxwell.Continuum.StoredHeaderEmissionData

/-! Complete execution of the physical header: eight generated naturals,
three canonical rational values, and the actually sampled dyadic detuning. -/
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem executes (energyPort : ℕ) (energyLower : 733 ≤ energyPort)
    (v : ℕ→ℕ) (B H J : ℕ) (hB : 34 ≤ B)
    (width : ∀i∈emissionInputs energyPort,(v i).bits.length ≤ B)
    (positive : ∀a∈fractions energyPort,0<prepared v a.2.2)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (emissionInputs energyPort) v s.val)
    (scratch : NatAssign.Scratch s.val) (oldHeader : WordCleanup.Bounded outputList H s.val)
    (oldCanonical : WordCleanup.Bounded RationalCanonical.StoredEmission.words J s.val) :
    ∃cost t,Executes input tape (code energyPort) cost s t ∧cost ≤ emissionCost B H J ∧
      t.val.output=(bits energyPort v).reverse++s.val.output ∧NatAssign.Scratch t.val ∧
      t.val.address=s.val.address ∧t.val.memory=s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      (∀i,i∉emissionWork→t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c0,a,e0,hc0,ba,za,wa,fa⟩:=prepare_executes v B H hB
    (fun i hi=>width i (Finset.mem_union_left _ hi)) input tape s
    (fun i hi=>bank i (Finset.mem_union_left _ hi)) scratch oldHeader
  have ba' : NatAssign.Bank (emissionIds energyPort) (prepared v) a.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with owned|saved
    · exact ba i owned
    · have outside:=retained_outside energyPort energyLower i saved
      have hout : i∉outputs:=fun h=>outside (Finset.mem_union_right _ h)
      rw [prepared_kept v i hout]
      exact word_of_eq (fa.tapes i outside) (bank i (Finset.mem_union_right _ saved))
  have wa' : ∀i∈emissionIds energyPort,(prepared v i).bits.length ≤ emissionWidth B := by
    intro i hi
    rcases Finset.mem_union.mp hi with owned|saved
    · exact (wa i owned).trans (le_max_left _ _)
    · rw [prepared_kept v i (fun h=>retained_outside energyPort energyLower i saved (Finset.mem_union_right _ h))]
      exact (width i (Finset.mem_union_right _ saved)).trans (le_max_right _ _)
  have canonicalA : WordCleanup.Bounded RationalCanonical.StoredEmission.words J a.val := by
    intro i hi
    by_cases small : i<4
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (za i small)⟩
    · have outside : i∉work := by
        simp only [RationalCanonical.StoredEmission.words,List.mem_cons,List.not_mem_nil,or_false] at hi
        simp only [work,outputs,outputList,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
        omega
      obtain ⟨bs,w,stored⟩:=oldCanonical i hi
      exact ⟨bs,w,BankArray.word_of_eq (fa.tapes i outside) stored⟩
  obtain ⟨c1,b,e1,hc1,out1,fb⟩:=StoredNatural.continuumHeader_executes (prepared v) (emissionWidth B)
    (fun i hi=>wa' i (emission_naturals energyPort i hi)) input tape a
    (fun i hi=>ba' i (emission_naturals energyPort i hi))
  have canonicalB : WordCleanup.Bounded RationalCanonical.StoredEmission.words (workspaceWidth B J) b.val := by
    intro i hi
    obtain ⟨bs,w,stored⟩:=canonicalA i hi
    exact ⟨bs,w.trans (le_max_left _ _),BankArray.word_of_eq (congrFun fb.2.2.2.2 i) stored⟩
  have zb : NatAssign.Scratch b.val:=fun i hi=>blank_of_eq (congrFun fb.2.2.2.2 i) (za i hi)
  obtain ⟨c2,c,e2,hc2,out2,_,zc,addrC,memC,inpC,rngC,keepC⟩:=
    RationalCanonical.StoredEmission.list_executes (fractions energyPort) (prepared v)
      (emissionWidth B) (workspaceWidth B J) (le_max_right _ _)
      (by
        intro q hq
        simp only [fractions,List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl <;> dsimp <;> omega)
      positive (fun q hq=>by
        have member:=fraction_ports energyPort q hq
        exact ⟨wa' _ member.1,wa' _ member.2.1,wa' _ member.2.2⟩)
      input tape b (fun q hq=>by
        have member:=fraction_ports energyPort q hq
        exact ⟨word_of_eq (congrFun fb.2.2.2.2 _) (ba' _ member.1),
          word_of_eq (congrFun fb.2.2.2.2 _) (ba' _ member.2.1),
          word_of_eq (congrFun fb.2.2.2.2 _) (ba' _ member.2.2)⟩) canonicalB zb
  have retainedC (i : ℕ) (hi : i=4506 ∨i=4510) : c.val.tapes i=s.val.tapes i := by
    rw [keepC i (by rcases hi with rfl|rfl <;> decide),congrFun fb.2.2.2.2 i,
      fa.tapes i (by rcases hi with rfl|rfl <;> decide)]
  have detuningMember (i : ℕ) (hi : i=4506 ∨i=4510) : i∈emissionInputs energyPort := by
    apply Finset.mem_union_right
    simp only [retained,Finset.mem_insert,Finset.mem_singleton]
    tauto
  obtain ⟨c3,t,e3,hc3,out3,ft⟩:=detuning_executes v B
    (width _ (detuningMember _ (Or.inl rfl))) (width _ (detuningMember _ (Or.inr rfl))) input tape c
    (word_of_eq (retainedC _ (Or.inl rfl)) (bank _ (detuningMember _ (Or.inl rfl))))
    (word_of_eq (retainedC _ (Or.inr rfl)) (bank _ (detuningMember _ (Or.inr rfl))))
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,?_,
    (fun i hi=>blank_of_eq (congrFun ft.2.2.2.2 i) (zc i hi)),
    ft.1.trans (addrC.trans (fb.1.trans fa.address)),
    ft.2.2.1.trans (memC.trans (fb.2.2.1.trans fa.memory)),
    ft.2.1.trans (inpC.trans (fb.2.1.trans fa.inputHead)),
    ft.2.2.2.1.trans (rngC.trans (fb.2.2.2.1.trans fa.randomCursor)),?_⟩
  · change c2 ≤ 3*RationalCanonical.StoredEmission.costBound (emissionWidth B) (workspaceWidth B J)+1 at hc2
    unfold emissionCost
    omega
  · rw [out3,out2,out1,fa.output]
    simp only [bits,List.reverse_append,List.append_assoc]
  · intro i hi
    have h:=Finset.notMem_union.mp hi
    exact (congrFun ft.2.2.2.2 i).trans ((keepC i h.2).trans
      ((congrFun fb.2.2.2.2 i).trans (fa.tapes i h.1)))

#print axioms executes
end Maxwell.Continuum.StoredHeader
