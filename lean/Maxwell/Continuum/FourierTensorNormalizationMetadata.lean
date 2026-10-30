import Maxwell.Continuum.FourierTensorComputedWorkspace
import Maxwell.Continuum.CalibrationNormalizationLayout
import Maxwell.Continuum.CalibrationNormalizationOutput

/-! Binary descriptors of the actual normalized calibration array remain
short even when its stored rational coordinates have long raw channels. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem memoryTable_descriptor (n width heap : ℕ) (hw : 0<width) (memory : ℕ→Bool) :
    descriptorWidth (Profile.Runtime.memoryTable n width heap hw memory)≤
      4*(heap.bits.length+n.bits.length+width.bits.length+4) := by
  have hp := RationalAccumulator.bits_mul_le n width
  have hn := RationalAccumulator.bits_add_le heap (n*width)
  have htwo := RationalAccumulator.bits_mul_le 2 n
  have hprod := RationalAccumulator.bits_mul_le (2*n) width
  have hd := RationalAccumulator.bits_add_le heap (2*n*width)
  rw [show (2:ℕ).bits.length=2 by decide] at htwo
  change width.bits.length+heap.bits.length+(heap+n*width).bits.length+
    (heap+2*n*width).bits.length+1≤_
  omega

theorem normalizedOutput_descriptor {n : ℕ} (a : CalibrationMatrix.Buffers n)
    (K P B heap D den : ℕ) (memory : ℕ→Bool) :
    descriptorWidth (PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable n K P B heap memory) D K P den)≤
      4*(heap.bits.length+n.bits.length+(PowerMachine.BufferNorm.outputWidth n K P B).bits.length+4) := by
  exact memoryTable_descriptor n (PowerMachine.BufferNorm.outputWidth n K P B) heap
    (PowerMachine.BufferNorm.Allocation.outputWidth_pos n K P B) memory

theorem normalizedOutput_clock {n : ℕ} (a : CalibrationMatrix.Buffers n)
    (K P B heap D den : ℕ) (memory : ℕ→Bool) :
    (PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable n K P B heap memory) D K P den).clock.length=
      PowerMachine.BufferNorm.outputWidth n K P B := by
  simp only [PowerMachine.BufferNorm.normalizedOutput,Table.filled,
    PowerMachine.BufferNorm.Allocation.outputTable,Profile.Runtime.memoryTable,List.length_replicate]

def normalizationSlotCoefficient (C : ℕ) : ℕ := 64*(C+4)^2

theorem normalizationSlot_polynomial {n K P B C ell b : ℕ}
    (hell : 0<ell) (hb : 33≤b) (hn : n≤C*ell^33) (hK : K≤C*ell)
    (hP : P≤C*ell) (hB : B≤C*ell^b) :
    PowerMachine.BufferNorm.outputWidth n K P B≤normalizationSlotCoefficient C*ell^(b+1) := by
  have he1 : 1≤ell^(b+1) := one_le_pow₀ hell
  have hel : ell≤ell^(b+1) := Nat.le_self_pow (by omega) ell
  have heb : ell^b≤ell^(b+1) := Nat.pow_le_pow_right hell (by omega)
  have he33 : ell^33≤ell^(b+1) := Nat.pow_le_pow_right hell (by omega)
  have hn' := hn.trans (Nat.mul_le_mul_left C he33)
  have hP' := hP.trans (Nat.mul_le_mul_left C hel)
  have hB' := hB.trans (Nat.mul_le_mul_left C heb)
  have hk1 : K+1≤(C+1)*ell := by nlinarith only [hK,hell]
  have hprod : (K+1)*B≤C*(C+1)*ell^(b+1) := by
    apply (Nat.mul_le_mul hk1 hB).trans_eq
    rw [pow_succ]
    ring
  have hpb := Machin.Runtime.nat_bits_le_self P
  unfold PowerMachine.BufferNorm.outputWidth PowerMachine.BufferNorm.normalizationWidth
    NeumannMachine.StoredPairing.workWidth normalizationSlotCoefficient
  nlinarith only [hn',hP',hB',hprod,hpb,he1]

def normalizationDescriptorCoefficient (C H b d : ℕ) : ℕ :=
  4*(Nat.clog 2 (H+1)+d+Nat.clog 2 (C+1)+33+
    Nat.clog 2 (normalizationSlotCoefficient C+1)+(b+1)+4)

theorem normalizedOutput_descriptor_linear {n K P B C ell b H d heap : ℕ}
    (a : CalibrationMatrix.Buffers n) (D den : ℕ) (memory : ℕ→Bool)
    (hell : 0<ell) (hb : 33≤b) (hn : n≤C*ell^33) (hK : K≤C*ell)
    (hP : P≤C*ell) (hB : B≤C*ell^b) (hheap : heap≤H*ell^d) :
    descriptorWidth (PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable n K P B heap memory) D K P den)≤
      normalizationDescriptorCoefficient C H b d*ell := by
  have hw := normalizationSlot_polynomial hell hb hn hK hP hB
  have ln := FiniteAlgorithm.lengthBits_polynomial hell 33 hn
  have lw := FiniteAlgorithm.lengthBits_polynomial hell (b+1) hw
  have lh := FiniteAlgorithm.lengthBits_polynomial hell d hheap
  rw [ModePrelude.lengthBits_eq] at ln lw lh
  apply (normalizedOutput_descriptor a K P B heap D den memory).trans
  unfold normalizationDescriptorCoefficient
  nlinarith only [ln,lw,lh,hell]

#print axioms normalizedOutput_descriptor_linear
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
