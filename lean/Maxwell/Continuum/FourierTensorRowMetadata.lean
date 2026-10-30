import Maxwell.Continuum.FourierTensorArithmeticWidth

/-! Only the binary descriptors of the calibration array enter the
repeated tensor workspace. Its large unary width clock is consumed
solely by the one-time row preparation. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def descriptorWidth {n : ℕ} (a : Table n) : ℕ :=
  a.width.length+a.basePositive.length+a.baseNegative.length+a.baseDenominator.length+1

def rowMetadataWidth (M L R P : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  2*descriptorWidth a+2*lengthBits (aliasArraySize R)+2*slotWidth M L R P+32

theorem descriptors_bound {n : ℕ} (a : Table n) :
    (addressValue a.width).bits.length≤descriptorWidth a ∧
      (addressValue a.basePositive).bits.length≤descriptorWidth a ∧
      (addressValue a.baseNegative).bits.length≤descriptorWidth a ∧
      (addressValue a.baseDenominator).bits.length≤descriptorWidth a := by
  have hw := TensorSetup.canonical_bits a.width
  have hp := TensorSetup.canonical_bits a.basePositive
  have hn := TensorSetup.canonical_bits a.baseNegative
  have hd := TensorSetup.canonical_bits a.baseDenominator
  unfold descriptorWidth
  omega

theorem buffer_metadata_computed (M L R P : ℕ) (a : Table (2*aliasArraySize R)) (memory : ℕ→Bool) :
    (buffer M L R P a memory).MetadataWidth (rowMetadataWidth M L R P a) := by
  rcases descriptors_bound a with ⟨hw,hp,hn,hd⟩
  have htwo := RationalAccumulator.bits_mul_le 2 (aliasArraySize R)
  have hproduct := RationalAccumulator.bits_mul_le (2*aliasArraySize R) (addressValue a.width)
  have hs1 := RationalAccumulator.bits_add_le (addressValue a.basePositive) (addressValue a.baseNegative)
  have hs2 := RationalAccumulator.bits_add_le (addressValue a.basePositive+addressValue a.baseNegative)
    (addressValue a.baseDenominator)
  have hs3 := RationalAccumulator.bits_add_le
    (addressValue a.basePositive+addressValue a.baseNegative+addressValue a.baseDenominator)
    (2*aliasArraySize R*addressValue a.width)
  have hheap : (heap R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)).bits.length≤
        2*descriptorWidth a+(aliasArraySize R).bits.length+5 := by
    rw [show (2:ℕ).bits.length=2 by decide] at htwo
    unfold heap
    omega
  have hcount : (RowArithmetic.rowCount R).bits.length≤(aliasArraySize R).bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    apply Nat.size_le_size
    change RowArithmetic.rowCount R≤RowArithmetic.rowCount R*3
    omega
  have h5 := RationalAccumulator.bits_mul_le 5 (RowArithmetic.rowCount R)
  have hslot := Machin.Runtime.nat_bits_le_self (slotWidth M L R P)
  change (Profile.Runtime.memoryTable _ _ _ _ memory).MetadataWidth _
  apply Profile.Runtime.memoryTable_metadata
  · unfold rowMetadataWidth;omega
  · rw [show (5:ℕ).bits.length=3 by decide] at h5
    unfold rowMetadataWidth
    rw [ModePrelude.lengthBits_eq]
    omega

def allocationInputWidth (M L R P : ℕ) {n : ℕ} (a : Table n) : ℕ :=
  M.bits.length+L.bits.length+R.bits.length+P.bits.length+descriptorWidth a+5

theorem allocationInputWidth_spec (M L R P : ℕ) {n : ℕ} (a : Table n) :
    5≤allocationInputWidth M L R P a ∧
      InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
        (addressValue a.baseNegative) (addressValue a.baseDenominator) (allocationInputWidth M L R P a) := by
  rcases descriptors_bound a with ⟨hw,hp,hn,hd⟩
  constructor
  · unfold allocationInputWidth;omega
  · intro i _
    unfold initial allocationInputWidth
    split_ifs <;> first | omega | simp

#print axioms buffer_metadata_computed
#print axioms allocationInputWidth_spec
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
