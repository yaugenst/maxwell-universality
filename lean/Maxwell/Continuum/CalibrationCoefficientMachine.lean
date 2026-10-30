import Maxwell.Continuum.CalibrationCoefficientInitialize
import Maxwell.Continuum.CalibrationCoefficientValues

/-! Complete executed generation of the padded literal coefficient table.
Its entries, positive denominators, raw widths, and layout are conclusions. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 7000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def generatedCoefficientCode : Code := .seq initializeCoefficientCode coefficientCode
def generatedCoefficientCost (R B W : ℕ) : ℕ :=
  initializeCoefficientCost R B W+coefficientCost R (countWidth B) W

theorem output_get_width {T : ℕ} (a : PartArray.Table T) (W : ℕ) (hm : a.MetadataWidth W)
    (s : Store) (ha : a.OutputReady s) (i : Fin T) : (a.get i).Width W := by
  have hbits (xs : List Bool) : (addressValue xs).bits.length≤xs.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)
  have hw : addressValue a.width≤W := by rw [← a.clock_length]; exact hm.clock
  exact ⟨(hbits _).trans ((ha.positive.length i).le.trans hw),
    (hbits _).trans ((ha.negative.length i).le.trans hw),
    (hbits _).trans ((ha.denominator.length i).le.trans hw)⟩

theorem generatedCoefficient_executes (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R))) (B W : ℕ) (hB : 101≤B)
    (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid) (hradius : n 311=R)
    (haValid : ∀ i, (a.get i).Valid) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : coefficientWidth (countWidth B)≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hword : BankArray.Word s.val 201 xs) :
    ∃ (cost : ℕ) (t : Store) (c : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R)))
        (vf : ℕ→Parts) (nf : ℕ→ℕ) (finalWord : List Bool),
      Executes input tape generatedCoefficientCode cost s t ∧ cost≤generatedCoefficientCost R B W ∧
      c.OutputReady t ∧ sameMetadata b c ∧ NatAssign.Bank emissionIds nf t.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤coefficientWidth (countWidth B)) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀ i, c.get i=NeumannMachine.paddedCoefficients (tableCoefficients c) i) ∧
      (∀ i, (tableCoefficients c i).Valid ∧ (tableCoefficients c i).Width W ∧
        (tableCoefficients c i).value=cachedCoefficientTable (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) i) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤coefficientBaseWidth (countWidth B) ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), BankArray.Word t.val k
        (if k=200 then a.width else if k=202 then a.basePositive else if k=203 then a.baseNegative
          else if k=204 then a.baseDenominator else a.clock)) ∧
      ContinuationFrame s.val t.val := by
  obtain ⟨c0,u,word0,e0,hc0,bank0,agree0,width0,radius0,_,a0,b0,z0,count0,len0,continuation0⟩ :=
    initializeCoefficient_executes R a b B W hB v n hn hw hp hradius hbMeta hfit hsep hdisjoint
      input tape xs hlen s hs hz ha hb hword
  let d := b.filled (fun _ => Parts.literal 0) 0
  have p0 := reset_keeps_parameter v 0 (by decide)
  have p1 := reset_keeps_parameter v 1 (by decide)
  have quasi : RawFree.quasiParts (resetParts v)=RawFree.quasiParts v := by
    funext k
    fin_cases k
    · exact reset_keeps_parameter v 16 (by decide)
    · exact reset_keeps_parameter v 17 (by decide)
    · exact reset_keeps_parameter v 18 (by decide)
  have hBF := countWidth_ge B
  have hmeta : d.MetadataWidth W :=
    ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
  obtain ⟨c1,t,c,vf,nf,word1,e1,hc1,out,metadata,bank,agree,width,parameters,radius,blank,
      source,matrix,padding,counter,len,headers,continuation1⟩ := coefficient_executes R a d (countWidth B) W (by omega)
    (by unfold NeumannMachine.tableSize; omega) (resetParts v) (initializedCoefficientNaturals v n)
    agree0 width0
    (fun k hk => by rw [reset_keeps_parameter v k hk]; exact ⟨(hp k hk).1.mono hBF,(hp k hk).2⟩)
    radius0 haValid (haMeta.mono hBF) hmeta hfit hsep hdisjoint
    (by simpa only [p0] using ht) (by simpa only [p1] using hE) (by simpa only [quasi] using hr)
    input tape word0 len0 u bank0 z0 a0 b0 count0
  have source' : ∀ i : Fin (aliasArraySize R),
      (c.get (sourceSlot R (by unfold NeumannMachine.tableSize; omega) i)).Valid ∧
      (c.get (sourceSlot R (by unfold NeumannMachine.tableSize; omega) i)).value=
        cachedForcing (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) i := by
    intro i
    simpa only [p0,p1,quasi] using source i
  have matrix' : ∀ k : Fin (aliasArraySize R*aliasArraySize R),
      (c.get (matrixSlot R (by unfold NeumannMachine.tableSize; omega) k)).Valid ∧
      (c.get (matrixSlot R (by unfold NeumannMachine.tableSize; omega) k)).value=
        cachedTransitionMatrix (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value)
          R (flatRow R k) (flatColumn R k) := by
    intro k
    simpa only [p0,p1,quasi] using matrix k
  obtain ⟨valid,value⟩ := tableCoefficients_values R c (v 0).value (v 1).value
    (fun j => (RawFree.quasiParts v j).value) (tableSource R a) source' matrix'
  have positive : 0<addressValue b.width := lt_of_lt_of_le
    (lt_of_lt_of_le (by omega : 0<B) hBF) ((coefficientWidth_ge (countWidth B)).trans hfit)
  have zeroWidth : (Parts.literal 0).Width (addressValue b.width) := by
    norm_num [Parts.Width,Parts.literal]
    exact positive
  have zero : ∀ i : Fin (NeumannMachine.tableSize (aliasArraySize R)),
      aliasArraySize R+aliasArraySize R*aliasArraySize R ≤ i.val → c.get i=Parts.literal 0 := by
    intro i hi
    rw [padding i hi]
    exact b.filled_get (fun _ => Parts.literal 0) (fun _ => zeroWidth) i
  refine ⟨c0+c1,t,c,vf,nf,word1,e0.seq e1,Nat.add_le_add hc0 hc1,out,metadata,bank,agree,width,
    (fun k hk => (parameters k hk).trans (reset_keeps_parameter v k hk)),radius,blank,
    tableCoefficients_padded c zero,?_,counter,len,headers,continuation0.trans continuation1⟩
  intro i
  exact ⟨valid i,output_get_width c W (sameMetadata_width d c metadata W hmeta) t out _,value i⟩

#print axioms generatedCoefficient_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
