import Maxwell.Continuum.CalibrationInverseAllocation
import Maxwell.Continuum.CalibrationNeumannConverted

/-! The inverse descriptor bank is assembled from actual returned table
headers, arithmetic scratch, and preserved runtime input words. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def assembledValues {n : ℕ} (a : PartArray.Table n) (allocated unused : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k=200 then addressValue a.width else if k=202 then addressValue a.basePositive
  else if k=203 then addressValue a.baseNegative else if k=204 then addressValue a.baseDenominator
  else if k∈Allocation.ids then allocated k else if k∈Finset.Icc 107 140 then unused k else 0

theorem assembled_values_inputs {m : ℕ} (a : PartArray.Table m) (v unused : ℕ → ℕ) :
    Descriptors.Inputs (assembledValues a (Allocation.outputValues v) unused)
      (v 300) (v 301) (v 302) 0 (v 304) := by
  have h := Allocation.output_values_input v
  constructor
  · simpa [assembledValues,Allocation.ids,Allocation.inputs] using h.dimension
  · simpa [assembledValues,Allocation.ids,Allocation.inputs] using h.width
  · simpa [assembledValues,Allocation.ids,Allocation.inputs] using h.heap
  · simpa [assembledValues,Allocation.ids,Allocation.inputs] using h.denominator
  · simpa [assembledValues,Allocation.ids,Allocation.inputs] using h.iterations

theorem assembled_bank {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ)
    (hcanonical : SourceLayout a heap) (allocated unused : ℕ → ℕ) (logical : ℕ → Parts)
    (s : Store) (ha : a.Ready s)
    (hallocated : NatAssign.Bank Allocation.ids allocated s.val)
    (hunused : NatAssign.Bank (Finset.Icc 107 140) unused s.val)
    (hraw : RationalDataflow.Ready PartArray.sharedSlots logical s) :
    NatAssign.Bank Descriptors.ids (assembledValues a allocated unused) s.val := by
  intro k hk
  by_cases h200 : k=200
  · subst k
    simp only [assembledValues,ite_true]
    change BankArray.Word s.val 200 (addressValue a.width).bits
    rw [←hcanonical.canonical]
    exact ha.width
  by_cases h202 : k=202
  · subst k
    simp only [assembledValues,ite_true,show (202:ℕ)≠200 by decide,ite_false]
    change BankArray.Word s.val 202 (addressValue a.basePositive).bits
    simpa only [hcanonical.positive,addressValue_bits] using ha.basePositive
  by_cases h203 : k=203
  · subst k
    simp only [assembledValues,ite_true,show (203:ℕ)≠200 by decide,show (203:ℕ)≠202 by decide,ite_false]
    change BankArray.Word s.val 203 (addressValue a.baseNegative).bits
    simpa only [hcanonical.negative,addressValue_bits] using ha.baseNegative
  by_cases h204 : k=204
  · subst k
    simp only [assembledValues,ite_true,show (204:ℕ)≠200 by decide,show (204:ℕ)≠202 by decide,
      show (204:ℕ)≠203 by decide,ite_false]
    change BankArray.Word s.val 204 (addressValue a.baseDenominator).bits
    simpa only [hcanonical.denominator,addressValue_bits] using ha.baseDenominator
  simp only [assembledValues,h200,h202,h203,h204,ite_false]
  by_cases hal : k∈Allocation.ids
  · rw [ite_eq_left hal]
    exact hallocated k hal
  rw [ite_eq_right hal]
  by_cases hu : k∈Finset.Icc 107 140
  · rw [ite_eq_left hu]
    exact hunused k hu
  rw [ite_eq_right hu]
  have hwork : k∈workPorts := by
    simp only [Descriptors.ids,Allocation.ids,Allocation.inputs,Allocation.headerIds,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton,not_or,not_and] at hk hal hu
    simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have hsmall : k<1000 := by
    simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hwork
    omega
  simpa only [dataValues_small logical hsmall] using hraw.1 k (Finset.mem_union_right _ hwork)

theorem assembled_width {n : ℕ} (a : PartArray.Table n) (allocated unused : ℕ → ℕ) (B : ℕ)
    (ha : a.MetadataWidth B) (hv : ∀ k∈Allocation.ids, (allocated k).bits.length≤B)
    (hu : ∀ k∈Finset.Icc 107 140, (unused k).bits.length≤B) :
    ∀ k∈Descriptors.ids, (assembledValues a allocated unused k).bits.length≤B := by
  have bits (xs : List Bool) : (addressValue xs).bits.length≤xs.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)
  intro k _
  unfold assembledValues
  split_ifs with _ _ _ _ hv' hu'
  · exact (bits a.width).trans ha.width
  · exact (bits a.basePositive).trans ha.basePositive
  · exact (bits a.baseNegative).trans ha.baseNegative
  · exact (bits a.baseDenominator).trans ha.baseDenominator
  · exact hv k hv'
  · exact hu k hu'
  · simp

#print axioms assembled_bank
#print axioms assembled_width

end Maxwell.Continuum.Calibration.NeumannMachine
