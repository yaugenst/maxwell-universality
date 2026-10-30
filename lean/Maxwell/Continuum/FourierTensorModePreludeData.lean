import Maxwell.Continuum.FourierTensorModeComponent

/-! The two physical row constants are computed from stored integer
parameters. All other shared rational registers start at literal zero. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def zeroValues : ℕ→Parts := fun _ => Parts.literal 0
def factorValues (M A : ℕ) : ℕ→Parts :=
  Function.update zeroValues 0 (PhysicalFactorMachine.factorParts M A)
def values (M A L : ℕ) : ℕ→Parts :=
  Function.update (factorValues M A) 1 (FrequencyScaleMachine.result M L)
def code : Code := .seq (PhysicalFactorMachine.sharedCode 0) (FrequencyScaleMachine.code 1)
def changed : Finset ℕ := PhysicalFactorMachine.workspace RowArithmetic.bank∪
  FrequencyScaleMachine.workspace RowArithmetic.bank
def factorWidth (A W : ℕ) : ℕ := 32*W+16*A+64
def costBound (A W : ℕ) : ℕ := 2^134*(A+W+16)^7

theorem zero_width (S : Finset ℕ) (W : ℕ) (hW : 1≤W) : WidthBank S W zeroValues := by
  intro i _
  exact (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono hW

theorem factor_width (M A W : ℕ) (hm : M.bits.length≤W) (ha : A.bits.length≤W) :
    (PhysicalFactorMachine.factorParts M A).Width (factorWidth A W) := by
  have hx := PhysicalFactorMachine.returned_output M A zeroValues
  have hp := PhysicalFactorMachine.returnedJoined_width ∅ M A W zeroValues
    (by intro i hi;simp at hi) hm ha 32 (by decide)
  have hd := PhysicalFactorMachine.returnedJoined_width ∅ M A W zeroValues
    (by intro i hi;simp at hi) hm ha 548 (by decide)
  rw [←hx]
  exact ⟨hp,by simp,hd⟩

theorem factorValues_width (M A W : ℕ) (hm : M.bits.length≤W) (ha : A.bits.length≤W) :
    WidthBank RowArithmetic.bank (factorWidth A W) (factorValues M A) := by
  intro i _
  by_cases hi : i=0
  · subst i;simpa only [factorValues,Function.update_self] using factor_width M A W hm ha
  · simpa only [factorValues,Function.update_of_ne hi,zeroValues] using
      (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono
        (by unfold factorWidth;omega : 1≤factorWidth A W)

theorem values_width (M A L W Wout : ℕ) (hm : M.bits.length≤W) (ha : A.bits.length≤W)
    (hl : L.bits.length≤W) (hout : factorWidth A W≤Wout) :
    WidthBank RowArithmetic.bank Wout (values M A L) := by
  intro i hi
  by_cases h1 : i=1
  · subst i
    simpa only [values,Function.update_self] using
      (ModeAllocation.frequency_scale_width M L).mono (by unfold factorWidth at hout;omega)
  · simpa only [values,Function.update_of_ne h1] using
      (factorValues_width M A W hm ha i hi).mono hout

theorem values_good (M A L : ℕ) (hm : 0<M) : Good RowArithmetic.bank (values M A L) := by
  intro i _
  by_cases h1 : i=1
  · subst i;simpa only [values,Function.update_self] using FrequencyScaleMachine.result_valid M L hm
  by_cases h0 : i=0
  · subst i
    simpa only [values,Function.update_of_ne (by decide : (0:ℕ)≠1),factorValues,Function.update_self] using
      PhysicalFactorMachine.factorParts_valid M A hm
  · simpa only [values,factorValues,Function.update_of_ne h1,Function.update_of_ne h0,zeroValues] using
      Parts.literal_valid 0

theorem values_canonical (M A L : ℕ) : ModePrepare.canonical (values M A L)=values M A L := by
  funext i
  by_cases hi : 2 ≤ i ∧ i<28
  · simp [ModePrepare.canonical,hi,values,factorValues,zeroValues,
      Function.update_of_ne (by omega : i≠1),Function.update_of_ne (by omega : i≠0)]
  · simp only [ModePrepare.canonical,hi,ite_false]

theorem values_factor (M A L : ℕ) (hm : 0<M) :
    (values M A L 0).value=Supercell.physicalFactorApprox M A := by
  simpa [values,factorValues] using PhysicalFactorMachine.factorParts_value M A hm

theorem values_scale (M A L : ℕ) : values M A L 1=FrequencyScaleMachine.result M L := by
  simp [values]

theorem cost_bound (A W : ℕ) :
    PhysicalFactorMachine.sharedCost A W+stageCost (factorWidth A W)≤costBound A W := by
  have hbase : factorWidth A W+2≤32*(A+W+16) := by unfold factorWidth;omega
  have hs := Nat.pow_le_pow_left hbase 2
  rw [mul_pow] at hs
  have h27 : (A+W+16)^2≤(A+W+16)^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (A+W+14)^7≤(A+W+16)^7 := Nat.pow_le_pow_left (by omega) 7
  have hc := Nat.mul_le_mul_left (2^130) h7
  have hd : stageCost (factorWidth A W)≤(2^96*32^2)*(A+W+16)^7 := calc
    _ ≤ 2^96*(32^2*(A+W+16)^2) := Nat.mul_le_mul_left _ hs
    _ = (2^96*32^2)*(A+W+16)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h27
  unfold PhysicalFactorMachine.sharedCost costBound
  nlinarith only [hc,hd,Nat.zero_le ((A+W+16)^7)]

#print axioms values_factor
#print axioms values_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
