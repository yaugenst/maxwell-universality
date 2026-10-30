import Maxwell.Continuum.FourierTensorAliasData

/-! One fixed row load copies the runtime alias index, performs five
actual indexed reads, then clears the shared query counter. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def aliasReadCode : Code := .seq (WordReplace.code 1099 201)
  (.seq (rowPlanCode 5 aliasReadPlan) (.call (TapeOps.clear 201)))
def aliasReadCost (W k : ℕ) : ℕ := 21*k+25+rowPlanCost 5 3 W aliasReadPlan

theorem aliasRead_executes {n D Q N : ℕ} (a : Table (5*n)) (b : Table (2*D))
    (W : ℕ) (hm : a.MetadataWidth W) (v : ℕ→Parts) (hw : WidthBank tensorBank W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length ≤ W)
    (hrange : addressValue xs<n) (s : Store) (hs : FactorReady a Q N b v s)
    (hr : Ready termBank v s) (hword : BankArray.Word s.val 1099 xs) :
    ∃cost t,Executes input tape aliasReadCode cost s t ∧ cost ≤ aliasReadCost W xs.length ∧
      FactorReady a Q N b (aliasLoaded a (addressValue xs) v) t ∧
      Ready termBank (aliasLoaded a (addressValue xs) v) t ∧
      WidthBank tensorBank W (aliasLoaded a (addressValue xs) v) ∧
      t.val.tapes 1048=s.val.tapes 1048 ∧ t.val.tapes 1099=s.val.tapes 1099 := by
  have hz201 : BankArray.Word s.val 201 [] := by
    have h := hs.setup 201 (by decide)
    simpa only [initialSetup,initialDimensions,show (201:ℕ)≠710 by decide,
      show (201:ℕ)≠711 by decide,ite_false,Word,Nat.zero_bits,BankArray.Word] using h
  obtain ⟨s0,e0,word0,f0⟩ := WordReplace.executes 1099 201 (by decide) input tape xs [] s hword hz201
  have r0 := hs.ready.wordReplace_frame (outside_workspace tensorBank 201 (by decide)) f0
  have a0 := hs.source.copy_frame (Or.inl rfl) f0
  have b0 := hs.output.copy_frame (Or.inl rfl) f0 a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,Blank s0.val i := by
    intro i hi
    have he : i≠201 := by simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    apply blank_of_eq (f0.2.2.2.2.2.1 i he)
    apply hs.floor.2
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    omega
  obtain ⟨c1,s1,e1,h1,r1,w1,a1,z1,f1⟩ := rowPlan_executes a tensorBank 5 3 W aliasReadPlan
    (by simp [aliasReadPlan,tensorBank,ids]) (by decide) hm v hw input tape xs hlen
    (by intro x hx;simp only [aliasReadPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega)
    s0 r0 a0 word0 z0
  have b1 := b0.rowPlan_frame f1 a1.scratch a1.seven
  obtain ⟨origin,word1⟩ := BankArray.word_of_eq f1.counter word0
  obtain ⟨t,e2,tapes2,f2⟩ := WordCall.clear 201 input tape xs origin s1 word1
  have cf2 : WordReplace.Frame 201 s1.val t.val :=
    ⟨f2.1,f2.2.1,f2.2.2.1,f2.2.2.2.1,f2.2.2.2.2.1,
      fun i hi => f2.2.2.2.2.2.1 i hi hi,
      fun i _ _ h26 h27 => f2.2.2.2.2.2.2 i h26 h27⟩
  have rt := r1.wordReplace_frame (outside_workspace tensorBank 201 (by decide)) cf2
  have at' := a1.copy_frame (Or.inl rfl) cf2
  have bt := b1.copy_frame (Or.inl rfl) cf2 at'.scratch at'.seven
  have zt : ∀i∈RowIndex.ids,Blank t.val i := by
    intro i hi
    exact blank_of_eq (cf2.2.2.2.2.2.1 i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega)) (z1 i hi)
  have countBlank : Blank t.val 201 := by
    refine ⟨origin+xs.length,?_⟩
    simp only [tapes2,Function.update_self]
  have keep (i : ℕ) (hi : 10 ≤ i) (hp : i∉ports tensorBank) (hrow : i∉RowIndex.ids) (hc : i≠201) :
      t.val.tapes i=s.val.tapes i :=
    (cf2.2.2.2.2.2.1 i hc).trans ((f1.tapes i hi hp hrow).trans (f0.2.2.2.2.2.1 i hc))
  have keepSmall (i : ℕ) (hi : 10 ≤ i) (hhi : i<1000) (hc : i≠201) (hrow : i∉RowIndex.ids) :
      t.val.tapes i=s.val.tapes i := by
    apply keep i hi _ hrow hc
    intro hm
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hm
    have hp := positivePort_ge j
    have hn := negativePort_ge j
    have hd := denominatorPort_ge j
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  have h4 : t.val.tapes 4=s.val.tapes 4 :=
    (cf2.2.2.2.2.2.1 4 (by decide)).trans
      ((e1.protectsTape 4 (by decide)).trans (f0.2.2.2.2.2.1 4 (by decide)))
  have fr := hs.restored_row_frame rt at' bt keepSmall h4 zt countBlank
  have tr : Ready termBank (aliasLoaded a (addressValue xs) v) t := by
    have rr := rt.partition hr (by
      intro j hj hjt i hi
      have hj32 : j=32 := by simpa only [termBank,Finset.mem_insert,hjt,or_false] using hj
      subst j
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl <;> exact keep _ (by decide) (by decide) (by decide) (by decide))
    apply rr.congr
    intro i hi
    by_cases hit : i∈tensorBank
    · exact ite_eq_left hit
    · have hi32 : i=32 := by simpa only [termBank,Finset.mem_insert,hit,or_false] using hi
      subst i
      simp only [ite_eq_right hit,aliasLoaded_keep a (addressValue xs) v 32 (by omega)]
  refine ⟨(6*[].length+15*xs.length+21)+(c1+(6*xs.length+4)),t,e0.seq (e1.seq e2),?_,
    fr,tr,w1,keep 1048 (by decide) (by decide) (by decide) (by decide),
    keep 1099 (by decide) (by decide) (by decide) (by decide)⟩
  unfold aliasReadCost
  simp only [List.length_nil]
  omega

#print axioms aliasRead_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
