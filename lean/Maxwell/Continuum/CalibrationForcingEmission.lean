import Maxwell.Continuum.CalibrationForcingPrepare
import Maxwell.Continuum.CalibrationForcingStored

/-! One iteration of the actual forcing-table emitter. Index decoding,
source reads, free inverse arithmetic, and output writes are all executed. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def forcingEmissionCode : Code := .seq forcingPrepareCode forcingRowCode
def forcingComputedParts (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) : ℕ→Parts :=
  forcingRowParts R a row (forcingDecodedParts v n row)
def forcingComputedNaturals (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (v : ℕ→Parts) (n : ℕ→ℕ) (row k : ℕ) : ℕ :=
  if k∈ids RawFree.neighborRegisters then dataValues (forcingComputedParts R a v n row) k
  else forcingDecodedNaturals v n row k

theorem inputReady_emission_frame {n : ℕ} (a : PartArray.Table n) (s t : Store)
    (ha : a.Ready s) (v : ℕ→Parts) (hr : RationalDataflow.Ready RawFree.neighborRegisters v t)
    (hf : BinaryPrecision.Frame emissionChanged s.val t.val) : a.Ready t := by
  have keep (k : ℕ) (hk : k∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ)) :=
    hf.tapes k (emission_protected k hk)
  refine ⟨⟨hr.2 0 (by decide),hr.2 1 (by decide),hr.2 2 (by decide),hr.2 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by simp)) ha.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by simp)) ha.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by simp)) ha.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by simp)) ha.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by simp)) ha.seven,
    BankArray.word_of_eq (keep 200 (by simp)) ha.width,
    BankArray.word_of_eq (keep 202 (by simp)) ha.basePositive,
    BankArray.word_of_eq (keep 203 (by simp)) ha.baseNegative,
    BankArray.word_of_eq (keep 204 (by simp)) ha.baseDenominator,
    BankArray.word_of_eq (keep 205 (by simp)) ha.clock,?_,?_,?_⟩
  · simpa only [hf.memory] using ha.positive
  · simpa only [hf.memory] using ha.negative
  · simpa only [hf.memory] using ha.denominator

theorem forcingComputed_parameter (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (v : ℕ→Parts) (n : ℕ→ℕ) (row k : ℕ) (hk : k∈matrixParameters) :
    forcingComputedParts R a v n row k=v k := by
  rw [forcingComputedParts,forcingRow_parameter _ _ _ _ k hk,forcingDecoded_parameter _ _ _ k hk]

theorem forcingComputed_agrees (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (v : ℕ→Parts) (n : ℕ→ℕ) (row k : ℕ) (hk : k∈ids RawFree.neighborRegisters) :
    forcingComputedNaturals R a v n row k=dataValues (forcingComputedParts R a v n row) k := by
  rw [forcingComputedNaturals,ite_eq_left hk]

theorem forcingComputed_radius (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (v : ℕ→Parts) (n : ℕ→ℕ) (row : ℕ) : forcingComputedNaturals R a v n row 311=n 311 := by
  rw [forcingComputedNaturals,ite_eq_right (by decide : 311∉ids RawFree.neighborRegisters),
    forcingDecoded_radius]

theorem forcingEmission_executes {T : ℕ} (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table T) (row : Fin (aliasRowCount R)) (hT : aliasArraySize R≤T)
    (v : ℕ→Parts) (n : ℕ→ℕ) (B W : ℕ) (hB : 2≤B)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤forcingEmissionWidth B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : (n 311).bits.length≤B) (hradius : n 311=R)
    (haValid : ∀ i, (a.get i).Valid) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : forcingEmissionWidth B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (hindex : addressValue xs=row.val) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hcounter : BankArray.Word s.val 201 xs) :
    ∃ cost t, Executes input tape forcingEmissionCode cost s t ∧
      cost≤2^1120*(forcingEmissionWidth B+W+10)^2 ∧
      NatAssign.Bank emissionIds (forcingComputedNaturals R a v n row.val) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (forcingComputedParts R a v n row.val) t ∧
      Good RawFree.neighborRegisters (forcingComputedParts R a v n row.val) ∧
      (∀ k∈emissionIds, (forcingComputedNaturals R a v n row.val k).bits.length≤forcingEmissionWidth B) ∧
      a.Ready t ∧
      (PartArray.rowWriteTable 3 row.val forcingWritePlan (forcingComputedParts R a v n row.val) b).OutputReady t ∧
      (∀ i : Fin 3, (forcingComputedParts R a v n row.val (37+i.val)).value=
        cachedForcing (v 0).value (v 1).value (fun k => (RawFree.quasiParts v k).value)
          R (tableSource R a) (polarizationRow R row i)) ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧ t.val.tapes 201=s.val.tapes 201 ∧ ContinuationFrame s.val t.val := by
  obtain ⟨c0,u,e0,hc0,bank0,ready0,good0,width0,wn0,coord0,blank0,frame0⟩ := forcingPrepare_executes
    v n B hB hn hw hp hR R row hradius input tape xs hlen hindex s hs hz hcounter
  have a0 := inputReady_emission_frame a s u ha _ ready0 frame0
  have b0 := outputReady_emission_frame b s u hb _ ready0 frame0
  have count0 := frame0.tapes 201 (by decide)
  have work0 : ∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank u.val k := by
    intro k hk
    have hwork : k∈NaturalQuotient.workPorts := (show PartArray.RowIndex.ids⊆NaturalQuotient.workPorts by decide) hk
    have word := bank0 k (emissionIds_work hwork)
    rw [forcingDecoded_work v n row.val k hwork,RationalAccumulator.zero_word_iff_blank] at word
    exact word
  have p0 := forcingDecoded_parameter v n row.val 0 (by decide)
  have p1 := forcingDecoded_parameter v n row.val 1 (by decide)
  have quasi : RawFree.quasiParts (forcingDecodedParts v n row.val)=RawFree.quasiParts v := by
    funext k
    fin_cases k
    · exact forcingDecoded_parameter v n row.val 16 (by decide)
    · exact forcingDecoded_parameter v n row.val 17 (by decide)
    · exact forcingDecoded_parameter v n row.val 18 (by decide)
  have hBB := forcingBaseWidth_ge B
  obtain ⟨c1,t,e1,hc1,ready1,good1,width1,a1,b1,value,work1,count1,four1,keep1⟩ := forcingRow_executes
    R a b row hT (forcingDecodedParts v n row.val) (forcingBaseWidth B) W (by omega)
    width0 good0 haValid (haMeta.mono hBB) hbMeta hfit hsep hdisjoint coord0
    (by simpa only [p0] using ht) (by simpa only [p1] using hE)
    (by simpa only [quasi] using hr) input tape xs (hlen.trans hBB) hindex u ready0 a0 b0
    (BankArray.word_of_eq count0 hcounter) work0
  have bank : NatAssign.Bank emissionIds (forcingComputedNaturals R a v n row.val) t.val := by
    intro k hk
    by_cases hraw : k∈ids RawFree.neighborRegisters
    · simpa only [forcingComputedNaturals,hraw,ite_true,forcingComputedParts] using ready1.1 k hraw
    · rw [forcingComputedNaturals,ite_eq_right hraw]
      by_cases hrow : k∈PartArray.RowIndex.ids
      · have hwork : k∈NaturalQuotient.workPorts :=
          (show PartArray.RowIndex.ids⊆NaturalQuotient.workPorts by decide) hrow
        rw [forcingDecoded_work v n row.val k hwork]
        exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (work1 k hrow)
      · have h37 : k≠37 := by intro he; subst k; exact (by decide : 37∉emissionIds) hk
        exact RationalAccumulator.word_of_eq (keep1 k (emissionIds_ge k hk) hraw hrow h37) (bank0 k hk)
  refine ⟨c0+c1,t,e0.seq e1,?_,bank,ready1,good1,?_,a1,b1,?_,?_,count1.trans count0,?_⟩
  · have hb := forcingEmissionWidth_ge B
    have hs0 : (forcingEmissionWidth B+10)^2≤(forcingEmissionWidth B+W+10)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hs1 : (forcingBaseWidth B+W+10)^2≤(forcingEmissionWidth B+W+10)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    nlinarith only [hc0,hc1,hs0,hs1,Nat.zero_le ((forcingEmissionWidth B+W+10)^2)]
  · intro k hk
    by_cases hraw : k∈ids RawFree.neighborRegisters
    · rw [forcingComputedNaturals,ite_eq_left hraw]
      exact dataValues_width _ _ _ width1 k hraw
    · rw [forcingComputedNaturals,ite_eq_right hraw]
      exact (wn0 k hk).trans (forcingEmissionWidth_ge B)
  · intro i
    simpa only [forcingComputedParts,p0,p1,quasi] using value i
  · intro k hk
    by_cases h4 : k<4
    · exact ready1.2 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq four1 (blank0 4 (by decide))

  · intro k hk
    have h := continuation_external k hk
    have hn : k∉ids RawFree.neighborRegisters := fun hh => h.2.1 (Finset.mem_union_right _ (emissionIds_parts hh))
    exact (keep1 k h.1 hn (fun hi => h.2.2.2.2 ((show PartArray.RowIndex.ids⊆NaturalQuotient.workPorts by decide) hi)) h.2.2.1).trans (frame0.tapes k h.2.1)

#print axioms forcingEmission_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
