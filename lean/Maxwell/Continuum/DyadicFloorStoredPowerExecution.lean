import Maxwell.Continuum.DyadicFloorStoredPowerData
import Maxwell.Continuum.DyadicFloorCost

/-! A single floor program reads its dyadic scale from memory. All arithmetic,
quotient steps and work-tape cleanup are charged; the scale word is preserved. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem lift_width (S : Finset ℕ) (P B : ℕ) (v : ℕ→ℕ)
    (hw : ∀i∈DyadicFloor.allIds S,(v i).bits.length≤B) (hp : P+1≤B) :
    ∀i∈allIds S,(withPower P v i).bits.length≤B := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl|hi
  · simpa only [withPower,Function.update_self,Nat.size_eq_bits_len,Nat.size_pow] using hp
  · have hne : i≠144 := fun h => power_outside S (h ▸ hi)
    simpa only [withPower,Function.update_of_ne hne] using hw i hi

theorem stage_executes (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid (allIds S)) (hl : ins.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈allIds S,(v i).bits.length≤B)
    (hc : ∀a∈ins,a.literalWidth≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank (allIds S) v s.val) (hz : ∀i,i<5→Blank s.val i) :
    ∃ cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank (allIds S) (NatAssign.values ins v) t.val ∧
      (∀i,i<5→Blank t.val i) ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hc,hb',hz',hf⟩ := fixedBankStage_executes (allIds S)
    (fun i hi => (by decide : 4≤10).trans (allIds_ge S i hi)) ins hv hl v B hw hc
    input tape s hb (fun i hi => hz i (by omega))
  refine ⟨cost,t,he,hc,hb',?_,hf.mono ?_⟩
  · intro i hi
    by_cases h4 : i<4
    · exact hz' i h4
    · have he : i=4 := by omega
      subst i
      apply blank_of_eq (hf.tapes 4 _) (hz 4 (by decide))
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨by omega,by intro hm;have := allIds_ge S 4 hm;omega⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hz|ht
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢;tauto))
    · rcases Finset.mem_insert.mp ht with rfl|ht
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ht)

theorem executes (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃ cost t,Executes input tape (code target source) cost s t ∧ cost≤DyadicFloor.costBound P W ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      Word t.val 144 (2^P) ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  have oldsub : DyadicFloor.allIds S⊆allIds S := Finset.subset_insert _ _
  have hmag : RationalMagnitude.ids⊆allIds S := (magnitude_mem S).trans oldsub
  have hext : ∀i∈extraIds,i∈allIds S := fun i hi => oldsub (extra_mem S i hi)
  have scratch : ∀i,i<5→Blank s.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact hs.2 i h4
    · have he : i=4 := by omega
      subst i
      exact hz.1
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes S (prepare source)
    (prepare_valid S source hs') (by simp [prepare,DyadicFloor.prepare])
    (withPower P (dataValues v)) (P+W+1) (initial_width S P v W hw)
    (by simp [prepare,DyadicFloor.prepare,NatAssign.Instruction.literalWidth])
    input tape s (initial_bank S P v s hs hz hp) scratch
  rw [prepare_values] at b0
  have hi30 : withPower P (beforeMagnitude P v source) 30=shiftedPositive P (v source) := by
    simpa only [withPower,Function.update_of_ne (by decide : (30:ℕ)≠144)]
      using (beforeMagnitude_inputs P v source).1
  have hi31 : withPower P (beforeMagnitude P v source) 31=scaledNegative P (v source) := by
    simpa only [withPower,Function.update_of_ne (by decide : (31:ℕ)≠144)]
      using (beforeMagnitude_inputs P v source).2.1
  have hi34 : withPower P (beforeMagnitude P v source) 34=0 := by
    simpa only [withPower,Function.update_of_ne (by decide : (34:ℕ)≠144)]
      using (beforeMagnitude_inputs P v source).2.2.1
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,_⟩ := RationalMagnitude.executes (allIds S) hmag
    (fun i hi => (by decide : 4≤10).trans (allIds_ge S i hi))
    (withPower P (beforeMagnitude P v source)) hi34 input tape s0 b0 (fun i hi => z0 i (by omega))
  have b1' : NatAssign.Bank (allIds S) (withPower P (afterMagnitude P v source)) s1.val := by
    rw [hi30,hi31,magnitude_eq P (v source) hx] at b1
    simpa only [afterMagnitude,withPower,Function.update_comm (by decide : (34:ℕ)≠144)] using b1
  have hc1 : c1≤300*(2*(2^10*(P+W+2))+4) := by
    rw [hi30,hi31] at h1
    have hh := beforeMagnitude_width S P v source W hs' hw
    have hp' := hh 30 (magnitude_mem S (by decide))
    have hn := hh 31 (magnitude_mem S (by decide))
    rw [(beforeMagnitude_inputs P v source).1] at hp'
    rw [(beforeMagnitude_inputs P v source).2.1] at hn
    exact h1.trans (Nat.mul_le_mul_left _ (by omega))
  have z1' : ∀i,i<5→Blank s1.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact z1 i h4
    · have he : i=4 := by omega
      subst i
      exact blank_of_eq (f1.tapes 4 (by decide)) (z0 4 (by decide))
  have hd : 0<withPower P (afterMagnitude P v source) 142 := by
    simpa [withPower,afterMagnitude,beforeMagnitude,Parts.Valid] using hx
  have hzero : ∀i∈NaturalQuotient.workPorts,withPower P (afterMagnitude P v source) i=0 := by
    intro i hi
    have ho := power_outside S
    have hne : i≠144 := by
      intro he;subst i;exact ho (Finset.mem_union_right _ hi)
    simpa only [withPower,Function.update_of_ne hne] using afterMagnitude_zero P v source i hi
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := NaturalQuotient.executes (allIds S) (allIds_ge S)
    (Finset.subset_union_right.trans oldsub) 34 142 140 (hmag (by decide))
    (hext 142 (by decide)) (hext 140 (by decide)) (by decide) (by decide) (by decide)
    (withPower P (afterMagnitude P v source)) hzero hd (workWidth P W)
    (lift_width S P _ _ (afterMagnitude_width S P v source W hs' hw hx) (by unfold workWidth;omega))
    input tape s1 b1' z1'
  have b2' : NatAssign.Bank (allIds S) (withPower P (divided P v source)) s2.val := by
    simpa [withPower,divided,afterMagnitude,beforeMagnitude,
      Function.update_comm (by decide : (140:ℕ)≠144)] using b2
  have hfinish : ∀a∈DyadicFloor.finish target,a.Valid (allIds S) := by
    intro a ha
    have hv := DyadicFloor.finish_valid S target ht a ha
    cases a <;> first
      | exact oldsub hv
      | exact ⟨oldsub hv.1,oldsub hv.2.1,hv.2.2⟩
  obtain ⟨c3,t,e3,h3,b3,z3,f3⟩ := stage_executes S (DyadicFloor.finish target) hfinish
    (by simp [DyadicFloor.finish,output,NatAssign.clearList_length,privateTapes])
    (withPower P (divided P v source)) (workWidth P W)
    (lift_width S P _ _ (divided_width S P v source W hs' hw hx) (by unfold workWidth;omega))
    (by
      intro a ha
      rcases List.mem_append.mp ha with ho|hz'
      · simp only [output,List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth,workWidth]
        omega
      · rw [NatAssign.clearList_literalWidth privateTapes a hz'];omega)
    input tape s2 b2' z2
  rw [finish_values S P v target source ht] at b3
  have hb3 : NatAssign.Bank (DyadicFloor.allIds S)
      (dataValues (Function.update v target (result P (v source)))) t.val := by
    intro i hi
    have hne : i≠144 := fun h => power_outside S (h ▸ hi)
    simpa only [withPower,Function.update_of_ne hne] using b3 i (oldsub hi)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,
    ⟨fun i hi => hb3 i (logical_mem S i hi),fun i hi => z3 i (by omega)⟩,?_,?_,
    f0.trans ((f1.mono ?_).trans ((f2.mono ?_).trans f3))⟩
  · unfold DyadicFloor.costBound;omega
  · refine ⟨z3 4 (by decide),?_⟩
    intro i hi
    have hh := hb3 i (by
      rcases Finset.mem_union.mp hi with he|hq
      · exact extra_mem S i he
      · exact Finset.mem_union_right _ hq)
    rw [dataValues_small _ (extra_small i hi)] at hh
    exact (zero_word_iff_blank _ _).mp hh
  · simpa only [withPower,Function.update_self] using b3 144 (Finset.mem_insert_self _ _)
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hm
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz' ⊢;tauto))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (magnitude_mem S hm))
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|ht'
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hz')
    · rcases Finset.mem_insert.mp ht' with rfl|ht'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ht')

#print axioms executes
end Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
