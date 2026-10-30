import Maxwell.Continuum.CalibrationCoefficientEmission
import Maxwell.Continuum.RationalDataflowArrayFill

/-! Padding and coefficient slots are initialized by actual memory writes.
No preinitialized denominator-one or zero-output array is assumed. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 7000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def initializeCoefficientCode : Code := .seq runtimeResetCode
  (.seq (tableCounterCode paddedCountPlan) (PartArray.fillCode 12))
def initializedCoefficientNaturals (v : ℕ→Parts) (n : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.values paddedCountPlan (cleanNaturals v n)
def initializeCoefficientCost (R B W : ℕ) : ℕ :=
  2^108*(B+3)^2+2^120*(2*B+10)^2+
  (NeumannMachine.tableSize (aliasArraySize R)+1)*(13*countWidth B+15)+
  NeumannMachine.tableSize (aliasArraySize R)*(2^30*(W+6)^2)

theorem fill12_protects (k : ℕ) (hk : (310≤k ∧ k≤332) ∨ k=223 ∨ k=4) :
    (PartArray.fillCode 12).protectsTape k=true := by
  rcases hk with hk | rfl | rfl
  · rcases hk with ⟨hlo,hhi⟩
    interval_cases k <;> decide
  · decide
  · decide


theorem fill12_continuation : ∀ k∈continuationPorts,
    (PartArray.fillCode 12).protectsTape k=true := by decide

theorem emission_external (k : ℕ) (hk : k∈emissionIds) (hr : k∉ids RawFree.neighborRegisters)
    (hw : k∉PartArray.RowIndex.ids) : (310≤k ∧ k≤332) ∨ k=223 := by
  rcases Finset.mem_union.mp hk with hk | hk
  · rcases Finset.mem_union.mp hk with hk | hk
    · exact False.elim (hr hk)
    · exact Or.inl (Finset.mem_Icc.mp hk)
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [PartArray.RowIndex.ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hw
    omega

theorem coefficientWidth_ge (B : ℕ) : B≤coefficientWidth B :=
  (countWidth_ge B).trans ((forcingEmissionWidth_base_ge (countWidth B)).trans
    ((countWidth_ge _).trans (emission_width_ge _)))

theorem initializedCoefficient_work (v : ℕ→Parts) (n : ℕ→ℕ) (k : ℕ)
    (hk : k∈NaturalQuotient.workPorts) : initializedCoefficientNaturals v n k=0 := by
  have hn : k∉countTargets := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [countTargets,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  rw [initializedCoefficientNaturals,countPlans_keep paddedCountPlan (Or.inr (Or.inr rfl)) _ k hn]
  exact (cleanNaturals_parameters v n).2.2 k hk

theorem initializeCoefficient_executes (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R))) (B W : ℕ) (hB : 101≤B)
    (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid) (hradius : n 311=R)
    (hbMeta : b.MetadataWidth W) (hfit : coefficientWidth (countWidth B)≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hword : BankArray.Word s.val 201 xs) :
    ∃ (cost : ℕ) (t : Store) (finalWord : List Bool),
      Executes input tape initializeCoefficientCode cost s t ∧ cost≤ initializeCoefficientCost R B W ∧
      NatAssign.Bank emissionIds (initializedCoefficientNaturals v n) t.val ∧
      (∀ k∈ids RawFree.neighborRegisters, initializedCoefficientNaturals v n k=dataValues (resetParts v) k) ∧
      (∀ k∈emissionIds, (initializedCoefficientNaturals v n k).bits.length≤countWidth B) ∧
      initializedCoefficientNaturals v n 311=R ∧
      RationalDataflow.Ready RawFree.neighborRegisters (resetParts v) t ∧
      a.Ready t ∧ (b.filled (fun _ => Parts.literal 0) 0).OutputReady t ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤countWidth B ∧ ContinuationFrame s.val t.val := by
  obtain ⟨c0,u0,e0,hc0,bank0,ready0,_,width0,z0,f0⟩ := runtimeReset_executes v n hn B B
    (by omega) le_rfl hw hp (hw 311 (by decide)) (hw 330 (by decide)) input tape s hs hz
  have a0 := inputReady_emission_frame a s u0 ha _ ready0 f0
  have b0 := outputReady_emission_frame b s u0 hb _ ready0 f0
  obtain ⟨c1,u1,e1,hc1,bank1,width1,ready1,a1,b1,z1,word1,continuation1⟩ := tableCounter_executes a b paddedCountPlan
    (Or.inr (Or.inr rfl)) (resetParts v) (cleanNaturals v n) B (by omega)
    (cleanNaturals_agrees v n) width0 input tape xs u0 bank0 z0 a0 b0
    (BankArray.word_of_eq (f0.tapes 201 (by decide)) hword)
  let nf := initializedCoefficientNaturals v n
  have radius : nf 311=R := by
    change initializedCoefficientNaturals v n 311=R
    rw [initializedCoefficientNaturals,countPlans_keep paddedCountPlan (Or.inr (Or.inr rfl)) _ 311 (by decide),
      (cleanNaturals_parameters v n).1,hradius]
  have count : nf 332=NeumannMachine.tableSize (aliasArraySize R) := by
    change initializedCoefficientNaturals v n 332=_
    rw [initializedCoefficientNaturals,paddedCount_value,(cleanNaturals_parameters v n).1,hradius]
  have agree : ∀ k∈ids RawFree.neighborRegisters, nf k=dataValues (resetParts v) k :=
    countPlans_agrees paddedCountPlan (Or.inr (Or.inr rfl)) (cleanNaturals v n) (resetParts v)
      (cleanNaturals_agrees v n)
  have zero : resetParts v 12=Parts.literal 0 := by rw [resetParts,ite_eq_left (by decide : 12∈resetSlots)]
  have hWB : countWidth B≤W := by
    have hb := coefficientWidth_ge (countWidth B)
    have hm : addressValue b.width≤W := by rw [← b.clock_length]; exact hbMeta.clock
    omega
  have widthPositive : 0<addressValue b.width :=
    lt_of_lt_of_le (lt_of_lt_of_le (by omega : 0<B) (countWidth_ge B))
      ((coefficientWidth_ge (countWidth B)).trans hfit)
  have zeroFit : (resetParts v 12).Width (addressValue b.width) := by
    rw [zero]
    norm_num [Parts.Width,Parts.literal]
    exact widthPositive
  have blankWork : ∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank u1.val k := by
    intro k hk
    have hwork := (show PartArray.RowIndex.ids⊆NaturalQuotient.workPorts by decide) hk
    have word := bank1 k (emissionIds_work hwork)
    change RationalAccumulator.Word u1.val k (initializedCoefficientNaturals v n k) at word
    rw [initializedCoefficient_work v n k hwork,RationalAccumulator.zero_word_iff_blank] at word
    exact word
  let ys := (nf 332).bits
  obtain ⟨origin,word⟩ := word1
  obtain ⟨c2,t,finalWord,e2,hc2,ready2,a2,b2,work2,counter2,len2⟩ := PartArray.fill_executes a b
    RawFree.neighborRegisters 12 (by decide) (resetParts v) W hbMeta widthPositive zeroFit hsep hdisjoint
    input tape ys origin ((width1 332 (by decide)).trans hWB) u1
    (by simp only [ys,addressValue_bits,count]) word ready1 a1 b1 blankWork
  have bank2 : NatAssign.Bank emissionIds nf t.val := by
    intro k hk
    by_cases hr : k∈ids RawFree.neighborRegisters
    · simpa only [agree k hr] using ready2.1 k hr
    · by_cases hrow : k∈PartArray.RowIndex.ids
      · change RationalAccumulator.Word t.val k (initializedCoefficientNaturals v n k)
        rw [initializedCoefficient_work v n k ((show PartArray.RowIndex.ids⊆NaturalQuotient.workPorts by decide) hrow)]
        exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (work2 k hrow)
      · have hprotect := fill12_protects k (by
          rcases emission_external k hk hr hrow with hc | hc
          · exact Or.inl hc
          · exact Or.inr (Or.inl hc))
        exact RationalAccumulator.word_of_eq (e2.protectsTape k hprotect) (bank1 k hk)
  refine ⟨c0+(c1+c2),t,finalWord,e0.seq (e1.seq e2),?_,bank2,agree,width1,radius,ready2,a2,?_,?_,
    ⟨origin,counter2⟩,len2.trans_le (width1 332 (by decide)),?_⟩
  · have h1 := hc1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : B+xs.length+10≤2*B+10) 2))
    have hlen2 : ys.length≤countWidth B := width1 332 (by decide)
    have h2 : c2≤(NeumannMachine.tableSize (aliasArraySize R)+1)*(13*countWidth B+15)+
        NeumannMachine.tableSize (aliasArraySize R)*(2^30*(W+6)^2) :=
      hc2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
    unfold initializeCoefficientCost
    omega
  · simpa only [zero] using b2
  · intro k hk
    by_cases h4 : k<4
    · exact ready2.2 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (e2.protectsTape 4 (fill12_protects 4 (Or.inr (Or.inr rfl))))
        (z1 4 (by decide))

  · intro k hk
    exact (e2.protectsTape k (fill12_continuation k hk)).trans
      ((continuation1 k hk).trans (continuation_of_frame f0 k hk))

#print axioms initializeCoefficient_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
