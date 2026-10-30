import Maxwell.Continuum.FourierTensorAllocatedInput
import Maxwell.Continuum.FourierTensorRegisterInitialization
import Maxwell.Continuum.FourierTensorModeGenerated

/-! The computed row table supplies canonical allocation headers; all
remaining cache inputs are retained runtime words or cleared scratch. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def CanonicalHeaders {n : ℕ} (a : Table n) : Prop :=
  a.width=(addressValue a.width).bits ∧ a.basePositive=(addressValue a.basePositive).bits ∧
    a.baseNegative=(addressValue a.baseNegative).bits ∧ a.baseDenominator=(addressValue a.baseDenominator).bits

theorem generated_headers (M L R P : ℕ) (a : Table (2*Calibration.aliasArraySize R))
    (j : Fin 3) (v : ℕ→Parts) (memory : ℕ→Bool) :
    CanonicalHeaders (ModeAllocation.generatedTable M L R P a j v memory) := by
  simp only [CanonicalHeaders,ModeAllocation.generatedTable,Table.filled,
    ModeAllocation.buffer,Profile.Runtime.memoryTable,addressValue_bits]
  trivial

theorem initial_bank {R Q N : ℕ} (a : Table (5*RowArithmetic.rowCount R))
    (hc : CanonicalHeaders a) (s : Store) (ha : a.Ready s)
    (hs : NatAssign.Bank setupIds (initialSetup Q N) s.val) (hr : Word s.val 311 R)
    (halloc : ∀i∈Profile.Runtime.CacheAllocation.inputs,Blank s.val i)
    (hn : Blank s.val 1100) (hd : Blank s.val 1110) :
    NatAssign.Bank ids (initial Q N R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val := by
  intro i hi
  by_cases hdim : i∈dimensionIds
  · simpa only [initial_dimensions Q N R _ _ _ _ i hdim,initialSetup] using
      hs i (by simp only [setupIds,Finset.mem_union];exact Or.inl (Or.inl hdim))
  have cases' : i=200 ∨ i=202 ∨ i=203 ∨ i=204 ∨ i=311 ∨ i∈Profile.Runtime.CacheAllocation.inputs ∨ i=1100 ∨ i=1110 := by
    have other := (Finset.mem_union.mp hi).resolve_left hdim
    simp only [Finset.mem_insert,Finset.mem_singleton] at other
    simp only [Profile.Runtime.CacheAllocation.inputs,Finset.mem_Icc]
    omega
  rcases cases' with rfl|rfl|rfl|rfl|rfl|hai|rfl|rfl
  · have word := ha.width
    rw [hc.1] at word
    simpa [initial,RationalAccumulator.Word,BankArray.Word] using word
  · have word := ha.basePositive
    rw [hc.2.1] at word
    simpa [initial,RationalAccumulator.Word,BankArray.Word] using word
  · have word := ha.baseNegative
    rw [hc.2.2.1] at word
    simpa [initial,RationalAccumulator.Word,BankArray.Word] using word
  · have word := ha.baseDenominator
    rw [hc.2.2.2] at word
    simpa [initial,RationalAccumulator.Word,BankArray.Word] using word
  · simpa [initial] using hr
  · have range := Finset.mem_Icc.mp hai
    have hz : initial Q N R (addressValue a.width) (addressValue a.basePositive)
        (addressValue a.baseNegative) (addressValue a.baseDenominator) i=0 := by
      unfold initial initialDimensions
      split_ifs <;> omega
    rw [hz,RationalAccumulator.zero_word_iff_blank]
    exact halloc i hai
  · simpa [initial,initialDimensions,RationalAccumulator.zero_word_iff_blank] using hn
  · simpa [initial,initialDimensions,RationalAccumulator.zero_word_iff_blank] using hd

theorem initial_width {R Q N W : ℕ} (a : Table (5*RowArithmetic.rowCount R))
    (ha : a.MetadataWidth W) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hR : R.bits.length≤W)
    (i : ℕ) : (initial Q N R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) i).bits.length≤W := by
  have hw := (canonical_bits a.width).trans ha.width
  have hp := (canonical_bits a.basePositive).trans ha.basePositive
  have hm := (canonical_bits a.baseNegative).trans ha.baseNegative
  have hd := (canonical_bits a.baseDenominator).trans ha.baseDenominator
  unfold initial initialDimensions
  split_ifs <;> first | assumption | simp

#print axioms generated_headers
#print axioms initial_bank
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
