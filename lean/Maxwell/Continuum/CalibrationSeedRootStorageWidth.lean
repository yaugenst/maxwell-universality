import Maxwell.Continuum.CalibrationSeedRootProducerData

/-! The fixed eight-term producer has an affine storage-width bound.
Its two constant coefficients can therefore be evaluated by fixed code. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
set_option exponentiation.threshold 2048

theorem guardedWidth_eq (B : ℕ) : guardedWidth B=indexWidth (testWidth B) := by
  apply max_eq_right
  unfold indexWidth testWidth
  change B≤128*(268435456*(B+3)+1)
  omega

theorem stepWidth_affine (B : ℕ) : stepWidth B=2^39*B+stepWidth 0 := by
  simp only [stepWidth,guardedWidth_eq,termWidth,indexWidth,testWidth]
  change 16*(128*(268435456*(B+3)+1)+2)=2^39*B+16*(128*(268435456*(0+3)+1)+2)
  ring

theorem termsWidth_affine (k B : ℕ) : termsWidth k B=(2^39)^k*B+termsWidth k 0 := by
  induction k generalizing B with
  | zero => simp [termsWidth]
  | succ k ih =>
    change termsWidth k (stepWidth B)=(2^39)^(k+1)*B+termsWidth k (stepWidth 0)
    rw [ih (stepWidth B),ih (stepWidth 0),stepWidth_affine B,pow_succ]
    ring

theorem producerWidth_affine (B : ℕ) : producerWidth B=2^321*B+producerWidth 0 := by
  change termsWidth parities.length (destinationWidth B)=
    2^321*B+termsWidth parities.length (destinationWidth 0)
  rw [termsWidth_affine _ (destinationWidth B),termsWidth_affine _ (destinationWidth 0)]
  simp only [show parities.length=8 by simp [parities],destinationWidth]
  ring

theorem producerWidth_pos (B : ℕ) : 0<producerWidth B := by
  have h:=producerWidth_ge_destination B
  unfold destinationWidth at h
  omega

theorem producerWidth_bits (B : ℕ) : (producerWidth B).bits.length≤B.bits.length+653 := by
  have a:=RationalAccumulator.bits_mul_le (2^321) B
  have b:=RationalAccumulator.bits_add_le (2^321*B) (producerWidth 0)
  have p : (2^321:ℕ).bits.length=322 := by decide
  have z : (producerWidth 0).bits.length≤330 := by decide
  rw [producerWidth_affine]
  omega

#print axioms producerWidth_affine
end Maxwell.Continuum.Calibration.SeedRoot
