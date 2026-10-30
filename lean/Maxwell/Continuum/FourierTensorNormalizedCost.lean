import Maxwell.Continuum.FourierTensorComputedPolynomial
import Maxwell.Continuum.FourierTensorNormalizationMetadata

/-! Tensor generation from the literal allocated calibration array. The
source and old output headers can represent that same normalized array;
the row allocator places its new storage beyond all three channels. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

def normalizationTensorCoefficient (C H b d : ℕ) : ℕ :=
  C+normalizationDescriptorCoefficient C H b d+2*normalizationSlotCoefficient C+1

theorem normalizedComponentCost_polylog (M A L R P Q N E K Pn B heap D den C H b d ell : ℕ)
    (a : CalibrationMatrix.Buffers (2*aliasArraySize R)) (memory : ℕ→Bool)
    (hell : 0<ell) (hb : 33≤b) (hbmax : b<2000)
    (hn : 2*aliasArraySize R≤C*ell^33) (hK : K≤C*ell)
    (hPn : Pn≤C*ell) (hB : B≤C*ell^b) (hheap : heap≤H*ell^d)
    (hw : ModePrelude.arithmeticWidth M A L R P Q N E≤C*ell)
    (hl : Q+N+ModePrelude.arithmeticWidth M A L R P Q N E+64≤C*ell^8) :
    let t := PowerMachine.BufferNorm.normalizedOutput a
      (PowerMachine.BufferNorm.Allocation.outputTable (2*aliasArraySize R) K Pn B heap memory) D K Pn den
    computedComponentCost M A L R P Q N E t t≤
      computedTimeCoefficient (normalizationTensorCoefficient C H b d)*ell^4096 := by
  let t := PowerMachine.BufferNorm.normalizedOutput a
    (PowerMachine.BufferNorm.Allocation.outputTable (2*aliasArraySize R) K Pn B heap memory) D K Pn den
  have hd : descriptorWidth t≤normalizationDescriptorCoefficient C H b d*ell :=
    normalizedOutput_descriptor_linear a D den memory hell hb hn hK hPn hB hheap
  have hs := normalizationSlot_polynomial hell hb hn hK hPn hB
  have hclock : t.clock.length=PowerMachine.BufferNorm.outputWidth (2*aliasArraySize R) K Pn B :=
    normalizedOutput_clock a K Pn B heap D den memory
  have hC : C≤normalizationTensorCoefficient C H b d := by
    unfold normalizationTensorCoefficient;omega
  have hD : normalizationDescriptorCoefficient C H b d≤normalizationTensorCoefficient C H b d := by
    unfold normalizationTensorCoefficient;omega
  have hi : ell≤ell^2000 := Nat.le_self_pow (by decide) ell
  have hp : ell^(b+1)≤ell^2000 := Nat.pow_le_pow_right hell (by omega)
  have hd' := hd.trans (Nat.mul_le_mul_left _ hi)
  have hs' := hs.trans (Nat.mul_le_mul_left _ hp)
  have hc : t.clock.length+tableWidth t≤normalizationTensorCoefficient C H b d*ell^2000 := by
    unfold tableWidth
    rw [hclock]
    apply (Nat.add_le_add hs' (Nat.add_le_add hd' hs')).trans
    calc
      _ = (normalizationDescriptorCoefficient C H b d+2*normalizationSlotCoefficient C)*ell^2000 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by unfold normalizationTensorCoefficient;omega)
  have hpos : 0<RowArithmetic.rowCount R := by
    unfold RowArithmetic.rowCount aliasSide
    positivity
  have hcount : RowArithmetic.rowCount R+1≤C*ell^33 := by
    apply le_trans _ hn
    change RowArithmetic.rowCount R+1≤2*(RowArithmetic.rowCount R*3)
    omega
  exact computedComponentCost_polylog M A L R P Q N E
    (normalizationTensorCoefficient C H b d) ell t t hell
    (hw.trans (Nat.mul_le_mul_right _ hC)) (hd.trans (Nat.mul_le_mul_right _ hD)) hc
    (hl.trans (Nat.mul_le_mul_right _ hC)) (hcount.trans (Nat.mul_le_mul_right _ hC))

#print axioms normalizedComponentCost_polylog
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
