import Maxwell.Continuum.FourierTensorPhysicalFactorSharedData

/-! Fixed physical-factor evaluation, copying and scratch cleanup, ready
for the next call on the same rational arithmetic bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def sharedCost (P W : ℕ) : ℕ := 2^130*(P+W+14)^7

theorem shared_cost (P W : ℕ) : costBound P W+stageCost (32*W+16*P+64)≤sharedCost P W := by
  have hp1 : 32*W+16*P+64+2≤32*(P+W+14) := by omega
  have hp2 := Nat.pow_le_pow_left hp1 2
  rw [mul_pow] at hp2
  have hp3 : (P+W+14)^2≤(P+W+14)^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hc : stageCost (32*W+16*P+64)≤(2^96*32^2)*(P+W+14)^7 := calc
    _ ≤ 2^96*(32^2*(P+W+14)^2) := Nat.mul_le_mul_left _ hp2
    _ = (2^96*32^2)*(P+W+14)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp3
  calc
    _ ≤ (2^120+2^96*32^2)*(P+W+14)^7 := by
      change 2^120*(P+W+14)^7+stageCost (32*W+16*P+64)≤_
      nlinarith only [hc]
    _ ≤ sharedCost P W := Nat.mul_le_mul_right _ (by norm_num)

theorem finishCall_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈finishCall target,a.Valid (allIds S) := by
  have hp := Finset.mem_union_left ids
    (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := Finset.mem_union_left ids
    (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := Finset.mem_union_left ids
    (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have hsmall (i : ℕ) (hi : i∈ids) : i∈allIds S := Finset.mem_union_right _ hi
  intro a ha
  rcases List.mem_append.mp ha with hc|hz
  · have hpg := positivePort_ge target
    have hdg := denominatorPort_ge target
    simp only [copyOutput,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨hsmall 32 (by decide),hp,by omega⟩
    · exact hn
    · exact ⟨hsmall 548 (by decide),hd,by omega⟩
  · exact NatAssign.clearList_valid _ _ (fun i hi => hsmall i
      (Finset.mem_union_left _ ((privateTapes_mem i).mp hi))) a hz

theorem finishCall_literalWidth (target : ℕ) : ∀a∈finishCall target,a.literalWidth=0 := by
  intro a ha
  rcases List.mem_append.mp ha with hc|hz
  · simp only [copyOutput,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl <;> rfl
  · exact NatAssign.clearList_literalWidth privateTapes a hz

theorem returnedJoined_width (S : Finset ℕ) (M P W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hm : M.bits.length≤W) (hp : P.bits.length≤W)
    (i : ℕ) (hi : i∈allIds S) : (returnedJoined M P v i).bits.length≤32*W+16*P+64 := by
  by_cases hx : i∈ids
  · simpa only [returnedJoined,ite_eq_left hx] using output_width M P W i hm hp
  · rw [returnedJoined,ite_eq_right hx]
    exact (dataValues_width S v W hw i ((Finset.mem_union.mp hi).resolve_right hx)).trans (by omega)

theorem shared_ready (S : Finset ℕ) (M P : ℕ) (v : ℕ→Parts) (t : Store)
    (hb : NatAssign.Bank (allIds S) (initialJoined M P v) t.val) (hz : NatAssign.Scratch t.val) :
    Ready S v t ∧ Clean t.val ∧ Word t.val 350 M ∧ Word t.val 351 P := by
  refine ⟨⟨?_,hz⟩,?_,?_,?_⟩
  · intro i hi
    have h350 : i≠350 := fun he => parameters_outside S i (Or.inl he) hi
    have h351 : i≠351 := fun he => parameters_outside S i (Or.inr he) hi
    simpa only [initialJoined,parameters,Function.update_of_ne h350,Function.update_of_ne h351] using
      hb i (Finset.mem_union_left _ hi)
  · intro i hi
    have h350 : i≠350 := fun he => (by decide : 350∉RationalRoot.ids) (he ▸ hi)
    have h351 : i≠351 := fun he => (by decide : 351∉RationalRoot.ids) (he ▸ hi)
    have h := hb i (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
    rw [initialJoined,parameters,Function.update_of_ne h351,Function.update_of_ne h350,
      dataValues_small v (ids_small i (Finset.mem_union_left _ hi))] at h
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp h
  · simpa [initialJoined,parameters] using hb 350 (Finset.mem_union_right _ (by decide))
  · simpa [initialJoined,parameters] using hb 351 (Finset.mem_union_right _ (by decide))

theorem shared_executes (S : Finset ℕ) (target M P W : ℕ) (v : ℕ→Parts)
    (ht : target∈S) (hM : 0<M) (hw : WidthBank S W v)
    (hm : M.bits.length≤W) (hp : P.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Clean s.val) (wm : Word s.val 350 M) (wp : Word s.val 351 P) :
    ∃cost t,Executes input tape (sharedCode target) cost s t ∧ cost≤sharedCost P W ∧
      Ready S (Function.update v target (factorParts M P)) t ∧ Clean t.val ∧
      Word t.val 350 M ∧ Word t.val 351 P ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  have initialBank := initialJoined_bank S M P v s hs hz wm wp
  have coreBank : NatAssign.Bank ids (initial M P) s.val := by
    intro i hi
    simpa only [initialJoined_small M P v i (ids_small i hi)] using
      initialBank i (Finset.mem_union_right _ hi)
  obtain ⟨c0,u,e0,hc0,b0,_,_,_,_,z0,f0⟩ := executes M P W hM hm hp input tape s coreBank hs.2
  have returned : NatAssign.Bank (allIds S) (returnedJoined M P v) u.val := by
    intro i hi
    by_cases hx : i∈ids
    · simpa only [returnedJoined,ite_eq_left hx] using b0 i hx
    · have hg := allIds_ge S i hi
      have hout : i∉changed := by
        simp only [changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hx
      simpa only [returnedJoined,ite_eq_right hx,initialJoined_outside M P v i hx] using
        RationalAccumulator.word_of_eq (f0.tapes i hout) (initialBank i hi)
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := fixedBankStage_executes (allIds S) (allIds_ge S)
    (finishCall target) (finishCall_valid S target ht) (by
      simp [finishCall,copyOutput,NatAssign.clearList_length,privateTapes])
    (returnedJoined M P v) (32*W+16*P+64) (returnedJoined_width S M P W v hw hm hp)
    (by intro a ha;rw [finishCall_literalWidth target a ha];omega) input tape u returned z0
  rw [finishCall_values] at b1
  have ready := shared_ready S M P (Function.update v target (factorParts M P)) t b1 z1
  refine ⟨c0+c1,t,e0.seq e1,?_,ready.1,ready.2.1,ready.2.2.1,ready.2.2.2,
    (f0.mono ?_).trans f1⟩
  · exact (Nat.add_le_add hc0 hc1).trans (shared_cost P W)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hi)

#print axioms shared_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
