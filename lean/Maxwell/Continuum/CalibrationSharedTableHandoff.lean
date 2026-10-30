import Maxwell.Continuum.CalibrationSharedTableCounter
import Maxwell.Continuum.CalibrationNeumannCopyPrepare

/-! Canonical descriptor words survive the executed table conversion and
are transported through the actual header swap. The denominator port is
obtained from the conversion output, without re-evaluating its product. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem conversion_protects : (List.range' 107 34 ++ List.range' 300 11).all
    (fun i => PartArray.sharedTableResetCode.protectsTape i)=true := by decide

theorem converted_descriptor_bank {n : ℕ} (a b : PartArray.Table n)
    (old new : ℕ → Parts) (v : ℕ → ℕ) {input : List Bool} {tape : ℕ → Bool}
    {cost : ℕ} {s t : Store}
    (he : Executes input tape PartArray.sharedTableResetCode cost s t)
    (hs : SharedConversion.Ready PartArray.sharedSlots old s)
    (ht : SharedConversion.Ready PartArray.sharedSlots new t)
    (ha : a.Ready s) (ha' : a.Ready t) (hb : b.OutputReady s)
    (hb' : (b.filled (SharedTable.integerParts a.get) 0).OutputReady t)
    (hv : NatAssign.Bank Descriptors.ids v s.val) : NatAssign.Bank Descriptors.ids v t.val := by
  intro i hi
  by_cases hwork : i ∈ workPorts
  · have hid : i ∈ SharedConversion.bankIds PartArray.sharedSlots :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hwork)
    have hsmall : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hwork
      omega
    have hold := hs.1 i hid
    have hnew := ht.1 i hid
    rw [dataValues_small old hsmall] at hold
    rw [dataValues_small new hsmall] at hnew
    exact word_recover (hv i hi) hold hnew
  · by_cases hp : i ∈ copyProtected
    · exact RationalAccumulator.word_of_eq (he.protectsTape i
        (List.all_eq_true.mp conversion_protects i (by
          simp only [copyProtected,Finset.mem_union,Finset.mem_Icc] at hp
          simp only [List.mem_append,List.mem_range'_1]
          omega))) (hv i hi)
    · have cases : i=200 ∨ i=202 ∨ i=203 ∨ i=204 ∨ i=210 ∨ i=212 ∨ i=213 ∨ i=214 := by
        simp only [Descriptors.ids,copyProtected,workPorts,temporaryPorts,RationalMagnitude.ids,
          Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi hp hwork
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact word_recover (hv _ hi) ha.width ha'.width
      · exact word_recover (hv _ hi) ha.basePositive ha'.basePositive
      · exact word_recover (hv _ hi) ha.baseNegative ha'.baseNegative
      · exact word_recover (hv _ hi) ha.baseDenominator ha'.baseDenominator
      · exact word_recover (hv _ hi) hb.width hb'.width
      · exact word_recover (hv _ hi) hb.basePositive hb'.basePositive
      · exact word_recover (hv _ hi) hb.baseNegative hb'.baseNegative
      · exact word_recover (hv _ hi) hb.baseDenominator hb'.baseDenominator

def swappedValues (v : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i=200 then v 210 else if i=202 then v 212 else if i=203 then v 213
  else if i=204 then v 214 else if i=210 then v 200 else if i=212 then v 202
  else if i=213 then v 203 else if i=214 then v 204 else v i

theorem word_relocate {s t : BitRAMState} {i j n : ℕ} {xs : List Bool}
    (hn : RationalAccumulator.Word s i n) (hx : BankArray.Word s i xs)
    (hy : BankArray.Word t j xs) : RationalAccumulator.Word t j n := by
  have he := word_unique hn hx
  rw [←he] at hy
  exact hy

theorem swapped_descriptor_bank {n m : ℕ} (a : PartArray.Table n) (b : PartArray.Table m)
    (v : ℕ → ℕ) {s t : Store} (ha : a.Ready s) (hb : b.OutputReady s)
    (ha' : a.OutputReady t) (hb' : b.Ready t)
    (f : BinaryPrecision.Frame (insert 216 PartArray.headerSlots) s.val t.val)
    (hv : NatAssign.Bank Descriptors.ids v s.val) :
    NatAssign.Bank Descriptors.ids (swappedValues v) t.val := by
  intro i hi
  simp only [swappedValues]
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · subst i
    exact word_relocate (hv 210 (by simp [Descriptors.ids])) hb.width hb'.width
  · subst i
    exact word_relocate (hv 212 (by simp [Descriptors.ids])) hb.basePositive hb'.basePositive
  · subst i
    exact word_relocate (hv 213 (by simp [Descriptors.ids])) hb.baseNegative hb'.baseNegative
  · subst i
    exact word_relocate (hv 214 (by simp [Descriptors.ids])) hb.baseDenominator hb'.baseDenominator
  · subst i
    exact word_relocate (hv 200 (by simp [Descriptors.ids])) ha.width ha'.width
  · subst i
    exact word_relocate (hv 202 (by simp [Descriptors.ids])) ha.basePositive ha'.basePositive
  · subst i
    exact word_relocate (hv 203 (by simp [Descriptors.ids])) ha.baseNegative ha'.baseNegative
  · subst i
    exact word_relocate (hv 204 (by simp [Descriptors.ids])) ha.baseDenominator ha'.baseDenominator
  · apply RationalAccumulator.word_of_eq (f.tapes i _) (hv i hi)
    simp only [Descriptors.ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton]
    omega

theorem computed_denominator_bank {S : Finset ℕ} (hzero : 0 ∈ S) (logical : ℕ → Parts)
    (D : ℕ) (hD : logical 0=⟨D,0,1⟩) (v : ℕ → ℕ) (s : Store)
    (hs : SharedConversion.Ready S logical s) (hv : NatAssign.Bank Descriptors.ids v s.val) :
    NatAssign.Bank CopyPlan.ids (Function.update v 1000 D) s.val := by
  intro i hi
  rcases Finset.mem_insert.mp hi with he | hi
  · subst i
    simp only [Function.update_self]
    have h := hs.1 (positivePort 0) (Finset.mem_union_left _ (cell_mem hzero (by simp [cellPorts])))
    rw [dataValues_positive,hD] at h
    simpa only [positivePort,Nat.mul_zero,Nat.add_zero] using h
  · have hne : i≠1000 := by
      simp only [Descriptors.ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    simpa only [Function.update_of_ne hne] using hv i hi

#print axioms converted_descriptor_bank
#print axioms computed_denominator_bank

end Maxwell.Continuum.Calibration.NeumannMachine
