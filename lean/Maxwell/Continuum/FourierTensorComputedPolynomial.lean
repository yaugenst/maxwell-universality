import Maxwell.Continuum.FourierTensorComputedCost

/-! A polynomial bound for the literal computed workspace, expressed in
actual calibration-array descriptors and clocks rather than free width
or preparation-cost parameters. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 32768

def computedTimeCoefficient (C : ℕ) : ℕ :=
  2^134*C^7+2^232*C*(4*(C+1))^2+tensorTimeCoefficient*C^3*(16*C)^243

theorem computedComponentCost_polylog {p : ℕ} (M A L R P Q N E C ell : ℕ)
    (a : Table (2*aliasArraySize R)) (old : Table p) (hell : 0<ell)
    (hw : ModePrelude.arithmeticWidth M A L R P Q N E≤C*ell)
    (hd : descriptorWidth a≤C*ell)
    (hc : a.clock.length+tableWidth old≤C*ell^2000)
    (hl : Q+N+ModePrelude.arithmeticWidth M A L R P Q N E+64≤C*ell^8)
    (hn : RowArithmetic.rowCount R+1≤C*ell^33) :
    computedComponentCost M A L R P Q N E a old≤computedTimeCoefficient C*ell^4096 := by
  have e18 : ell≤ell^8 := Nat.le_self_pow (by decide) ell
  have e12000 : ell≤ell^2000 := Nat.le_self_pow (by decide) ell
  have e0 : 1≤ell^2000 := one_le_pow₀ hell
  have hw' := hw.trans (Nat.mul_le_mul_left C e12000)
  have hd' := hd.trans (Nat.mul_le_mul_left C e12000)
  have hp : preparationDataSize M A L R P Q N E a old≤4*(C+1)*ell^2000 := by
    unfold preparationDataSize
    nlinarith only [hw',hd',hc,e0]
  have hd8 := hd.trans (Nat.mul_le_mul_left C e18)
  have ht : descriptorLoopSize M A L R P Q N E a≤16*C*ell^8 := by
    unfold descriptorLoopSize
    nlinarith only [hl,hd8]
  have ep : ell^4033≤ell^4096 := Nat.pow_le_pow_right hell (by decide)
  have et : ell^2043≤ell^4096 := Nat.pow_le_pow_right hell (by decide)
  have ei : ell^7≤ell^4096 := Nat.pow_le_pow_right hell (by decide)
  have hi : (ModePrelude.arithmeticWidth M A L R P Q N E)^7≤C^7*ell^4096 := by
    apply (Nat.pow_le_pow_left hw 7).trans
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ ei
  have hp' : (RowArithmetic.rowCount R+1)*(preparationDataSize M A L R P Q N E a old)^2≤
      (C*(4*(C+1))^2)*ell^4096 := by
    apply (Nat.mul_le_mul hn (Nat.pow_le_pow_left hp 2)).trans
    calc
      _ = (C*(4*(C+1))^2)*ell^4033 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ ep
  have ht' : (RowArithmetic.rowCount R+1)^3*(descriptorLoopSize M A L R P Q N E a)^243≤
      (C^3*(16*C)^243)*ell^4096 := by
    apply (Nat.mul_le_mul (Nat.pow_le_pow_left hn 3) (Nat.pow_le_pow_left ht 243)).trans
    calc
      _ = (C^3*(16*C)^243)*ell^2043 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ et
  apply (computedComponentCost_bound M A L R P Q N E a old).trans
  have h := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left (2^134) hi)
    (Nat.mul_le_mul_left (2^232) hp')) (Nat.mul_le_mul_left tensorTimeCoefficient ht')
  simpa only [computedTimeCoefficient,Nat.add_mul,Nat.mul_assoc] using h

#print axioms computedComponentCost_polylog
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
