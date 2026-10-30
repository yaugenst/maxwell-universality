import Maxwell.Continuum.FourierTensorComputedWorkspace

/-! The exact component cost separates the binary table descriptors from
the unary calibration clock. Only the quadratic preparation reads the
unreduced calibration entries. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem arithmetic_parameters (M A L R P Q N E : ℕ) :
    A+ModePrelude.inputWidth M A L+16≤ModePrelude.arithmeticWidth M A L R P Q N E ∧
    slotWidth M L R P≤ModePrelude.arithmeticWidth M A L R P Q N E ∧
    P≤ModePrelude.arithmeticWidth M A L R P Q N E ∧
    waveWorkBits (8*Q) N≤ModePrelude.arithmeticWidth M A L R P Q N E ∧
    32≤ModePrelude.arithmeticWidth M A L R P Q N E := by
  simp only [ModePrelude.arithmeticWidth,ModePrelude.factorWidth,ModePrelude.inputWidth,
    ModePrelude.lengthBits_eq,slotWidth]
  omega

theorem computedWorkWidth_bound (M A L R P Q N E : ℕ)
    (a : Table (2*aliasArraySize R)) :
    computedWorkWidth M A L R P Q N E a≤
      6*ModePrelude.arithmeticWidth M A L R P Q N E+2*descriptorWidth a := by
  have hs := (arithmetic_parameters M A L R P Q N E).2.1
  have h32 := (arithmetic_parameters M A L R P Q N E).2.2.2.2
  have hn := (ModePrelude.arithmeticWidth_spec M A L R P Q N E).2.2.2.1
  unfold computedWorkWidth rowMetadataWidth
  rw [ModePrelude.lengthBits_eq]
  omega

theorem allocationInputWidth_bound (M A L R P Q N E : ℕ) {n : ℕ} (a : Table n) :
    allocationInputWidth M L R P a≤ModePrelude.arithmeticWidth M A L R P Q N E+descriptorWidth a := by
  have hs := (arithmetic_parameters M A L R P Q N E).2.1
  have hp := Machin.Runtime.nat_bits_le_self P
  unfold slotWidth at hs
  unfold allocationInputWidth
  omega

def preparationDataSize {p : ℕ} (M A L R P Q N E : ℕ)
    (a : Table (2*aliasArraySize R)) (old : Table p) : ℕ :=
  ModePrelude.arithmeticWidth M A L R P Q N E+descriptorWidth a+a.clock.length+tableWidth old+1

def descriptorLoopSize (M A L R P Q N E : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  Q+N+8*(ModePrelude.arithmeticWidth M A L R P Q N E+descriptorWidth a)+64

theorem computedPreparation_bound {p : ℕ} (M A L R P Q N E : ℕ)
    (a : Table (2*aliasArraySize R)) (old : Table p) :
    preparationSize M L R P Q N (computedInputWidth M A L R P Q N E a)
      (computedWorkWidth M A L R P Q N E a) (allocationInputWidth M L R P a) (tableWidth old)≤
      32*preparationDataSize M A L R P Q N E a old := by
  obtain ⟨_,hs,hP,hw,h32⟩ := arithmetic_parameters M A L R P Q N E
  have hwork := computedWorkWidth_bound M A L R P Q N E a
  have halloc := allocationInputWidth_bound M A L R P Q N E a
  unfold preparationSize computedInputWidth preparationDataSize tableWidth
  omega

theorem computedLoop_bound (M A L R P Q N E : ℕ) (a : Table (2*aliasArraySize R)) :
    Q+N+computedWorkWidth M A L R P Q N E a+64≤descriptorLoopSize M A L R P Q N E a := by
  have hw := computedWorkWidth_bound M A L R P Q N E a
  unfold descriptorLoopSize
  omega

theorem computedComponentCost_bound {p : ℕ} (M A L R P Q N E : ℕ)
    (a : Table (2*aliasArraySize R)) (old : Table p) :
    computedComponentCost M A L R P Q N E a old≤
      2^134*(ModePrelude.arithmeticWidth M A L R P Q N E)^7+
      2^232*(RowArithmetic.rowCount R+1)*(preparationDataSize M A L R P Q N E a old)^2+
      tensorTimeCoefficient*(RowArithmetic.rowCount R+1)^3*(descriptorLoopSize M A L R P Q N E a)^243 := by
  have hprelude := Nat.mul_le_mul_left (2^134)
    (Nat.pow_le_pow_left (arithmetic_parameters M A L R P Q N E).1 7)
  have hp := Nat.mul_le_mul_left (2^222*(RowArithmetic.rowCount R+1))
    (Nat.pow_le_pow_left (computedPreparation_bound M A L R P Q N E a old) 2)
  have hp' : 2^222*(RowArithmetic.rowCount R+1)*
      (preparationSize M L R P Q N (computedInputWidth M A L R P Q N E a)
        (computedWorkWidth M A L R P Q N E a) (allocationInputWidth M L R P a) (tableWidth old))^2≤
      2^232*(RowArithmetic.rowCount R+1)*(preparationDataSize M A L R P Q N E a old)^2 := by
    convert hp using 1
    ring
  have ht := Nat.mul_le_mul_left (tensorTimeCoefficient*(RowArithmetic.rowCount R+1)^3)
    (Nat.pow_le_pow_left (computedLoop_bound M A L R P Q N E a) 243)
  simpa only [computedComponentCost,completeComponentCost,ModePrelude.costBound,componentCost,
    Nat.add_assoc] using Nat.add_le_add hprelude (Nat.add_le_add hp' ht)

#print axioms computedComponentCost_bound
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
