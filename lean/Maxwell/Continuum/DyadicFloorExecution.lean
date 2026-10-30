import Maxwell.Continuum.DyadicFloorStages

/-! Charged execution of exact dyadic floor from runtime Parts words. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def costBound (P W : ℕ) : ℕ :=
  stageCost (P+W+1)+300*(2*(2^10*(P+W+2))+4)+
    2^100*(workWidth P W+2)^2+stageCost (workWidth P W)

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
    simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto

theorem afterMagnitude_zero (P : ℕ) (v : ℕ→Parts) (source : ℕ) :
    ∀i∈NaturalQuotient.workPorts,afterMagnitude P v source i=0 := by
  intro i hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> simp [afterMagnitude,beforeMagnitude,dataValues]

theorem executes (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) (hz : Clean s.val) :
    ∃ cost t,Executes input tape (code P target source) cost s t ∧ cost≤costBound P W ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have scratch : ∀i,i<5→Blank s.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact hs.2 i h4
    · have he : i=4 := by omega
      subst i
      exact hz.1
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes S (prepare P source)
    (prepare_valid S P source hs') (by simp [prepare]) (dataValues v) (P+W+1)
    (fun i hi => (initial_width S v W hw i hi).trans (by omega))
    (fun a ha => (prepare_literalWidth P source a ha).trans (by omega))
    input tape s (initial_bank S v s hs hz) scratch
  rw [prepare_values] at b0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,_⟩ := RationalMagnitude.executes (allIds S) (magnitude_mem S)
    (fun i hi => (by decide : 4≤10).trans (allIds_ge S i hi)) (beforeMagnitude P v source)
    (beforeMagnitude_inputs P v source).2.2.1 input tape s0 b0 (fun i hi => z0 i (by omega))
  have b1' : NatAssign.Bank (allIds S) (afterMagnitude P v source) s1.val := by
    simpa only [afterMagnitude,(beforeMagnitude_inputs P v source).1,
      (beforeMagnitude_inputs P v source).2.1,magnitude_eq P (v source) hx] using b1
  have hc1 : c1≤300*(2*(2^10*(P+W+2))+4) := by
    have hp := beforeMagnitude_width S P v source W hs' hw 30 (magnitude_mem S (by decide))
    have hn := beforeMagnitude_width S P v source W hs' hw 31 (magnitude_mem S (by decide))
    exact h1.trans (Nat.mul_le_mul_left _ (by omega))
  have z1' : ∀i,i<5→Blank s1.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact z1 i h4
    · have he : i=4 := by omega
      subst i
      exact blank_of_eq (f1.tapes 4 (by decide)) (z0 4 (by decide))
  have hd : 0<afterMagnitude P v source 142 := by
    simpa [afterMagnitude,beforeMagnitude,Parts.Valid] using hx
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := NaturalQuotient.executes (allIds S) (allIds_ge S)
    Finset.subset_union_right 34 142 140 (magnitude_mem S (by decide))
    (extra_mem S 142 (by decide)) (extra_mem S 140 (by decide))
    (by decide) (by decide) (by decide) (afterMagnitude P v source)
    (afterMagnitude_zero P v source) hd (workWidth P W) (afterMagnitude_width S P v source W hs' hw hx)
    input tape s1 b1' z1'
  have b2' : NatAssign.Bank (allIds S) (divided P v source) s2.val := by
    simpa [divided,afterMagnitude,beforeMagnitude] using b2
  obtain ⟨c3,t,e3,h3,b3,z3,f3⟩ := stage_executes S (finish target)
    (finish_valid S target ht) (by simp [finish,output,NatAssign.clearList_length,privateTapes])
    (divided P v source) (workWidth P W) (divided_width S P v source W hs' hw hx)
    (by
      intro a ha
      rcases List.mem_append.mp ha with ho|hz'
      · simp only [output,List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth,workWidth]
        omega
      · rw [NatAssign.clearList_literalWidth privateTapes a hz']
        omega) input tape s2 b2' z2
  rw [finish_values] at b3
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,
    ⟨fun i hi => b3 i (logical_mem S i hi),fun i hi => z3 i (by omega)⟩,?_,
    f0.trans ((f1.mono ?_).trans (f2.trans f3))⟩
  · unfold costBound
    omega
  · refine ⟨z3 4 (by decide),?_⟩
    intro i hi
    have hb := b3 i (by
      rcases Finset.mem_union.mp hi with he|hq
      · exact extra_mem S i he
      · exact Finset.mem_union_right _ hq)
    rw [dataValues_small _ (extra_small i hi)] at hb
    exact (zero_word_iff_blank _ _).mp hb
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hm
    · apply Finset.mem_union_left
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz' ⊢
      tauto
    · exact Finset.mem_union_right _ (magnitude_mem S hm)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.DyadicFloor
