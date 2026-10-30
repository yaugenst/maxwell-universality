import Maxwell.Continuum.CalibrationSharedTableHandoff
import Maxwell.Continuum.CalibrationNeumannPrepared

/-! The literal raw coefficient table is converted, exchanged into the
input descriptor, copied, and consumed by the inverse loop by one fixed
runtime program. No inverse-loop snapshot is an input hypothesis. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem SourceLayout.separated {n : ℕ} {a : PartArray.Table (tableSize n)} {heap : ℕ}
    (h : SourceLayout a heap) : a.Separated := by
  simp only [PartArray.Table.Separated,h.positive,h.negative,h.denominator,addressValue_bits,
    IncidenceEncoding.Separated,Nat.mul_assoc]
  exact ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩

theorem sharedReady_subset {S T : Finset ℕ} (hST : S ⊆ T) {logical : ℕ → Parts} {s : Store}
    (hs : SharedConversion.Ready T logical s) : SharedConversion.Ready S logical s := by
  refine ⟨fun i hi => hs.1 i ?_,hs.2⟩
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j,hST hj,hi⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  · exact Finset.mem_union_right _ hi

theorem swappedValues_width (v : ℕ → ℕ) (B : ℕ)
    (hv : ∀ i ∈ Descriptors.ids, (v i).bits.length ≤ B) :
    ∀ i ∈ Descriptors.ids, (swappedValues v i).bits.length ≤ B := by
  intro i hi
  simp only [swappedValues]
  split_ifs <;> apply hv <;> first | exact hi | simp [Descriptors.ids]

def convertedValues (v : ℕ → ℕ) (D : ℕ) : ℕ → ℕ := Function.update (swappedValues v) 1000 D

theorem convertedValues_width (v : ℕ → ℕ) (D B : ℕ)
    (hv : ∀ i ∈ Descriptors.ids, (v i).bits.length ≤ B) (hD : D.bits.length ≤ B) :
    ∀ i ∈ CopyPlan.ids, (convertedValues v D i).bits.length ≤ B := by
  intro i hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i
    simpa only [convertedValues,Function.update_self] using hD
  · have hne : i≠1000 := by
      simp only [Descriptors.ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    simpa only [convertedValues,Function.update_of_ne hne] using swappedValues_width v B hv i hi

theorem convertedValues_inputs (v : ℕ → ℕ) (n width heap D N : ℕ)
    (hi : Descriptors.Inputs v n width heap 0 N) :
    CopyPlan.Inputs (convertedValues v D) n width heap D N := by
  constructor <;> simp [convertedValues,swappedValues,hi.dimension,hi.width,hi.heap,hi.iterations]

def convertedCode : Code :=
  .seq PartArray.sharedTableResetCode (.seq PartArray.headerSwapCode preparedCode)

def convertedCost (n width heap D N W B rawWidth countWidth : ℕ) : ℕ :=
  PartArray.sharedTableResetCost (tableSize n) W width countWidth+256*(width+1)+
    preparedCost n width heap D N B rawWidth

theorem converted_executes {n : ℕ} (hnpos : 0<n) (coeff : CoefficientIndex n → Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hW : 0<W)
    (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (haValues : ∀ i, a.get i=paddedCoefficients coeff i)
    (haMeta : a.MetadataWidth W) (hbMeta : b.MetadataWidth (addressValue b.width))
    (hl : SourceLayout b heap) (hdisjoint : a.SeparatedFrom b)
    (hshared : PartArray.sharedWidth (tableSize n) W ≤ B)
    (hprepare : 2^CopyPlan.plan.length*(B+1) ≤ addressValue b.width)
    (hslot : commonWidth n N (W+1) ≤ addressValue b.width)
    (haddress : heap.bits.length+2*n.bits.length+(addressValue b.width).bits.length+10 ≤
      addressValue b.width)
    (logical : ℕ → Parts) (hlogicalWidth : WidthBank PartArray.sharedSlots W logical)
    (v : ℕ → ℕ) (hi : Descriptors.Inputs v n (addressValue b.width) heap 0 N)
    (hbits : ∀ i ∈ Descriptors.ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length ≤ W) (s : Store) (hn : addressValue xs=tableSize n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (hs : SharedConversion.Ready PartArray.sharedSlots logical s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (h206 : RationalAccumulator.Blank s.val 206) (h216 : RationalAccumulator.Blank s.val 216) :
    ∃ (cost : ℕ) (t : Store) (out : Snapshot n), Executes input tape convertedCode cost s t ∧
      cost ≤ convertedCost n (addressValue b.width) heap (SharedTable.denominator coeff) N W B
        (addressValue a.width) xs.length ∧
      out.Ready n.bits
        (initializedWidth n (addressValue b.width) heap (SharedTable.denominator coeff) N
          (addressValue b.width)) t.val ∧
      out.data.Sized (initializedWidth n (addressValue b.width) heap (SharedTable.denominator coeff) N
        (addressValue b.width)) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 N ∧
      ∀ i : Fin n, ((Horner.channels out.words 10 11).value i : ℚ) /
          (SharedTable.denominator coeff : ℚ)^(N+1) =
        rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) (N+1) i := by
  have hBwidth : B ≤ addressValue b.width := by
    have hp : 1 ≤ 2^CopyPlan.plan.length := Nat.one_le_pow _ _ (by decide)
    have hh := Nat.mul_le_mul_right (B+1) hp
    omega
  have hwide := hshared.trans hBwidth
  have hWW : W ≤ addressValue b.width := by
    have hh : W ≤ PartArray.sharedWidth (tableSize n) W := by unfold PartArray.sharedWidth; nlinarith
    exact hh.trans hwide
  have hw : 0<addressValue b.width := lt_of_lt_of_le hW hWW
  have haWidth (i) : (a.get i).Width W := by rw [haValues]; exact padded_width coeff W hW hwidth i
  have haValid (i) : (a.get i).Valid := by rw [haValues]; exact padded_valid coeff hvalid i
  have haeq : a.get=paddedCoefficients coeff := funext haValues
  have denominator : SharedTable.denominator a.get=SharedTable.denominator coeff := by
    rw [haeq,denominator_padded]
  have intWidth (i) : (SharedTable.integerParts a.get i).Width (addressValue b.width) := by
    apply (SharedTable.integerParts_width a.get W haWidth i).mono
    simp only [Fintype.card_fin]
    exact (by unfold PartArray.sharedWidth; nlinarith :
      (tableSize n+1)*W+1 ≤ PartArray.sharedWidth (tableSize n) W).trans hwide
  let filled := b.filled (SharedTable.integerParts a.get) 0
  have filledValues (i) : filled.get i=SharedTable.integerParts (paddedCoefficients coeff) i := by
    rw [PartArray.Table.filled_get b _ intWidth,haeq]
  have filledWidth (i) : (filled.get i).Width (addressValue b.width) := by
    rw [PartArray.Table.filled_get b _ intWidth]
    exact intWidth i
  have filledMeta : filled.MetadataWidth (addressValue b.width) :=
    ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
  have filledLayout : SourceLayout filled heap :=
    ⟨hl.canonical,hl.positive,hl.negative,hl.denominator⟩
  obtain ⟨c0,u,out,e0,hc0,hu,ha',hb',hD,houtWidth,houtGood,count⟩ :=
    PartArray.sharedTable_reset_executes a b W (addressValue b.width) hW haWidth haValid
      haMeta hbMeta hwide hwide hl.separated hdisjoint logical hlogicalWidth
      input tape xs origin hlen s hn hcount hs ha hb h206
  have bank0 := converted_descriptor_bank a b logical out v e0 hs hu ha ha' hb hb' hbank
  have temp := RationalAccumulator.blank_of_eq (e0.protectsTape 216 (by decide)) h216
  obtain ⟨c1,u1,e1,hc1,_,b1,a1,_,frame1⟩ := PartArray.headerSwap_executes a filled
    (addressValue b.width) (haMeta.mono hWW) filledMeta PartArray.sharedSlots out
      input tape u hu.rational ha' hb' temp
  have state1 := shared_headerSwap_frame hu frame1
  have bank1 := swapped_descriptor_bank a filled v ha' hb' a1 b1 frame1 bank0
  have outputD : out 0=⟨SharedTable.denominator coeff,0,1⟩ := by simpa only [denominator] using hD
  have newBank := computed_denominator_bank (by decide : 0∈PartArray.sharedSlots) out
    (SharedTable.denominator coeff) outputD (swappedValues v) u1 state1 bank1
  have Dwidth : (SharedTable.denominator coeff).bits.length ≤ B := by
    rw [←denominator]
    apply (SharedTable.denominator_width a.get W haWidth).trans
    simp only [Fintype.card_fin]
    exact (by unfold PartArray.sharedWidth; nlinarith :
      tableSize n*W+1 ≤ PartArray.sharedWidth (tableSize n) W).trans hshared
  have newWidth : WidthBank {1} (addressValue b.width) out := by
    intro i hi
    have hi' : i=1 := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact (houtWidth 1 (by decide)).mono hwide
  have newGood : Good {1} out := by
    intro i hi
    have hi' : i=1 := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact houtGood (by unfold tableSize; omega)
  have count1 := BankArray.word_of_eq (frame1.tapes 201 (by decide)) count
  obtain ⟨countOrigin,count1⟩ := count1
  obtain ⟨c2,t,result,e2,hc2,ht,sized,denominatorWord,counter,hresult⟩ := prepared_executes coeff hvalid W hwidth filled a heap N B
    hw filledLayout filledValues hslot filledWidth filledMeta haddress hprepare out newWidth newGood
    (convertedValues v (SharedTable.denominator coeff))
    (convertedValues_inputs v n (addressValue b.width) heap (SharedTable.denominator coeff) N hi)
    (convertedValues_width v (SharedTable.denominator coeff) B hbits Dwidth)
    input tape xs countOrigin (hlen.trans hWW) u1 hn count1 newBank
    (sharedReady_subset (by decide : ({1} : Finset ℕ) ⊆ PartArray.sharedSlots) state1) b1 a1
  refine ⟨c0+(c1+c2),t,result,e0.seq (e1.seq e2),?_,ht,sized,denominatorWord,counter,hresult⟩
  change c2 ≤ preparedCost n (addressValue b.width) heap (SharedTable.denominator coeff) N B
    (addressValue a.width) at hc2
  unfold convertedCost
  omega

#print axioms converted_executes

end Maxwell.Continuum.Calibration.NeumannMachine
