import Maxwell.Continuum.CalibrationNormalizationWidths
import Maxwell.Continuum.CalibrationNormalizedArray
import Maxwell.Continuum.CalibrationNormalizedCounter

/-! Complete fixed-code normalization of the actual power buffer. The norm,
common denominator, output scaling, and every coordinate write are executed. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow RationalDataflow.PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def outputCode : Code := .seq scaleCode (.seq NormalizedEntry.counterCode NormalizedEntry.arrayCode)
def outputCost (n K P B length : ℕ) : ℕ := boundedScaleCost n K P B+
  (15*length+21)+NormalizedEntry.arrayCost n (outputWidth n K P B) length
def outputFresh : Finset ℕ := normalizationFresh∪{550,551,552,560,561}
def outputInitialValues (scale denominator : ℕ) (i : ℕ) : ℕ :=
  if i=551 then scale else if i=552 then denominator else 0

def normalizedOutput {n : ℕ} (a : Buffers n) (b : Table n) (D K P den : ℕ) : Table n :=
  b.filled (NormalizedEntry.entry (data a) den (D^(K+1)*Nat.sqrt (arrayNormRadicand a D K P))) 0

theorem output_executes {n : ℕ} (a : Buffers n) (b : Table n) (D K P B : ℕ) (count : List Bool)
    (hB : 1≤B) (hDpos : 0<D) (hD : D.bits.length≤B) (hK : K.bits.length≤B)
    (hsize : a.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (hbMeta : b.MetadataWidth (outputWidth n K P B))
    (hslot : outputWidth n K P B≤addressValue b.width) (hsep : b.Separated)
    (hdisjoint : NormalizedEntry.SeparatedFrom (data a) b)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : a.Ready count B s.val) (hb : b.OutputReady s)
    (hden : Word s.val 126 D) (hiterations : Word s.val 304 K) (hprecision : Word s.val 544 P)
    (hindex : Blank s.val 140) (hfresh : ∀ i∈outputFresh, Blank s.val i) :
    ∃ cost t den, Executes input tape outputCode cost s t ∧ cost≤outputCost n K P B count.length ∧
      0<den ∧ (normalizedOutput a b D K P den).OutputReady t ∧
      CalibrationMatrix.Stored (data a) t.val ∧
      (∀ i, ((normalizedOutput a b D K P den).get i).value=
        (arrayNormCenter a D K P)⁻¹*(((bufferChannels a).value i:ℚ)/(D^(K+1):ℕ))) ∧
      (0<arrayNormCenter a D K P → ∀ i, ((normalizedOutput a b D K P den).get i).Valid) := by
  obtain ⟨c0,u,den,e0,hc0,denPos,denWidth,factorBank,factorValue,scratch,seven,
      memory,arrayStored,keep,externalKeep⟩ := scale_executes a D K P B count hB hDpos hD hK
    hsize hcount hcl input tape s ha hden hiterations hprecision
    (fun i hi => hfresh i ((by
      intro j hj
      simp only [outputFresh,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
      tauto : normalizationFresh∪{550,551,552}⊆outputFresh) hi))
  let T := arrayNormRadicand a D K P
  let denom := D^(K+1)*Nat.sqrt T
  let W := outputWidth n K P B
  let initial := outputInitialValues den denom
  obtain ⟨vi,hvi,hvl,cal,originalStored,indices,out,countWord,rest⟩ := ha
  have radWidth := arrayNormRadicand_width a D K P hsize hD originalStored
  have powWidth := denominatorPower_width n D K P B hD
  have fullWidth := factor_output_width n D K P B T den radWidth denWidth powWidth
  have hcost0 : c0≤boundedScaleCost n K P B := hc0.trans
    (Nat.add_le_add_left (factor_cost_bound n D K P B T den radWidth denWidth powWidth) _)
  have bank : NatAssign.Bank NormalizedEntry.ids initial u.val := by
    intro i hi
    simp only [NormalizedEntry.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · simpa [initial,outputInitialValues,Factor.outputValues] using factorBank 551 (by decide)
    · simpa [initial,denom,outputInitialValues,Factor.outputValues] using factorBank 552 (by decide)
    all_goals
      simpa [initial,outputInitialValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr
        (RationalAccumulator.blank_of_eq (keep _ (by decide)) (hfresh _ (by simp [outputFresh])))
  have bankWidth : ∀ i∈NormalizedEntry.ids, (initial i).bits.length≤W := by
    intro i hi
    simp only [NormalizedEntry.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · simpa [initial,outputInitialValues,Factor.outputValues,W] using fullWidth 551
    · simpa [initial,denom,outputInitialValues,Factor.outputValues,W] using fullWidth 552
    all_goals simp [initial,outputInitialValues]
  have outputReady : b.OutputReady u := by
    apply hb.transfer memory _ scratch seven
    intro i hi
    exact externalKeep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [normalizationExternal,Finset.mem_insert,Finset.mem_singleton]
      tauto)
  have actualCount : BankArray.Word u.val 107 count :=
    BankArray.word_of_eq (externalKeep 107 (by simp [normalizationExternal])) countWord
  have blankIndex : Blank u.val 140 :=
    RationalAccumulator.blank_of_eq (externalKeep 140 (by simp [normalizationExternal])) hindex
  obtain ⟨v,e1,b1,a1,o1,w1,_⟩ := NormalizedEntry.counter_executes (data a) b initial count
    input tape u bank arrayStored outputReady actualCount blankIndex
  obtain ⟨origin,indexWord⟩ := w1
  have guard := output_scale_guard a K P den hsize denWidth
  have denBound : denom.bits.length≤W := by
    simpa [Factor.outputValues,denom] using fullWidth 552
  have hW : 0<W := by unfold W outputWidth; omega
  have hBW : B≤W := by
    unfold W outputWidth normalizationWidth NeumannMachine.StoredPairing.workWidth
    omega
  obtain ⟨c2,t,finalWord,finalValues,e2,hc2,a2,o2,_⟩ := NormalizedEntry.array_executes
    (data a) b den denom W hW (output_data_sized a K P hsize) hbMeta guard denBound hslot hsep
    hdisjoint initial (by simp [initial,outputInitialValues])
    (by simp [initial,outputInitialValues]) bankWidth input tape count origin (hcl.trans hBW) v
    hcount indexWord b1 a1 o1
  have fit (i : Fin n) : (NormalizedEntry.entry (data a) den denom i).Width (addressValue b.width) :=
    (NormalizedEntry.entry_width (data a) den denom W guard denBound a2 i).mono hslot
  refine ⟨c0+((15*count.length+21)+c2),t,den,e0.seq (e1.seq e2),?_,denPos,o2,a2,?_,?_⟩
  · unfold outputCost
    change c2≤NormalizedEntry.arrayCost n (outputWidth n K P B) count.length at hc2
    omega
  · intro i
    rw [normalizedOutput,Table.filled_get b _ fit,NormalizedEntry.entry_value]
    have scalar : (den:ℚ)/denom=(arrayNormCenter a D K P)⁻¹/(D^(K+1):ℕ) := by
      simpa only [Factor.factor,Parts.value,Nat.cast_zero,sub_zero] using factorValue
    rw [scalar]
    simp only [data,bufferChannels,Channels.value,Int.cast_sub,Int.cast_natCast]
    ring
  · intro hnorm i
    have positive : 0<denom := by
      by_contra hh
      have hz : denom=0 := Nat.eq_zero_of_not_pos hh
      have hzero : (Factor.factor T den (D^(K+1))).value=0 := by
        change ((den:ℚ)-0)/(denom:ℕ)=0
        simp [hz]
      have hp : (0:ℚ)<(arrayNormCenter a D K P)⁻¹/(D^(K+1):ℕ) := by
        exact div_pos (inv_pos.mpr hnorm) (by positivity)
      rw [hzero] at factorValue
      linarith
    rw [normalizedOutput,Table.filled_get b _ fit]
    exact positive

#print axioms output_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
