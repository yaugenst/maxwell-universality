import Maxwell.Continuum.FourierTensorModeInput

/-! Preparation costs keep the calibration-array width separate from
the small tensor workspace used in every output coefficient iteration. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 32768

def componentCode (j : Fin 3) : Code := .seq (generatedCode j)
  (.seq RowHandoff.code (.seq TensorStart.code tensorComponentCode))
def preparationSize (M L R P Q N Win Wout Wsetup H : ℕ) : ℕ :=
  P+Win+Wout+Wsetup+H+slotWidth M L R P+waveWorkBits (8*Q) N+32
def componentCost (M L R P Q N Win Wout Wsetup H : ℕ) : ℕ :=
  2^222*(RowArithmetic.rowCount R+1)*(preparationSize M L R P Q N Win Wout Wsetup H)^2+
    tensorTimeCoefficient*(RowArithmetic.rowCount R+1)^3*(Q+N+Wout+64)^243

theorem preparation_cost (M L R P Q N Win Wout Wsetup H : ℕ) :
    2^218*(RowArithmetic.rowCount R+1)*(P+Win+Wsetup+H+slotWidth M L R P+20)^2+
      (2^12*(P+Win+(2^8*(2^32*(Wsetup+1)+1))+4)^2+
        2^184*(Wout+Win+waveWorkBits (8*Q) N+16)^2)≤
      2^222*(RowArithmetic.rowCount R+1)*(preparationSize M L R P Q N Win Wout Wsetup H)^2 := by
  let X := preparationSize M L R P Q N Win Wout Wsetup H
  have h0 : (P+Win+Wsetup+H+slotWidth M L R P+20)^2≤X^2 :=
    Nat.pow_le_pow_left (by dsimp [X,preparationSize];omega) 2
  have h1 : P+Win+(2^8*(2^32*(Wsetup+1)+1))+4≤2^41*X := by
    dsimp [X,preparationSize]
    omega
  have h2 := Nat.pow_le_pow_left h1 2
  rw [mul_pow] at h2
  have h3 : (Wout+Win+waveWorkBits (8*Q) N+16)^2≤X^2 :=
    Nat.pow_le_pow_left (by dsimp [X,preparationSize];omega) 2
  have scaled := Nat.mul_le_mul_left (2^218*(RowArithmetic.rowCount R+1)) h0
  have hn : X^2≤(RowArithmetic.rowCount R+1)*X^2 := Nat.le_mul_of_pos_left _ (by omega)
  change _≤2^222*(RowArithmetic.rowCount R+1)*X^2
  nlinarith only [scaled,h2,h3,hn,Nat.zero_le (X^2)]

theorem componentCost_polylog (M L R P Q N Win Wout Wsetup H C ell : ℕ) (hell : 1≤ell)
    (hp : preparationSize M L R P Q N Win Wout Wsetup H≤C*ell^2000)
    (ht : Q+N+Wout+64≤C*ell^16) (hn : RowArithmetic.rowCount R+1≤C*ell^33) :
    componentCost M L R P Q N Win Wout Wsetup H≤
      (2^222*C^3+tensorTimeCoefficient*C^246)*ell^4096 := by
  have psmall := Nat.pow_le_pow_left hp 2
  have tsmall := Nat.pow_le_pow_left ht 243
  have nsmall := Nat.pow_le_pow_left hn 3
  have hprep := Nat.mul_le_mul hn psmall
  have hterm := Nat.mul_le_mul nsmall tsmall
  have ep : ell^(4033:ℕ)≤ell^4096 := Nat.pow_le_pow_right hell (by decide)
  have et : ell^(3987:ℕ)≤ell^4096 := Nat.pow_le_pow_right hell (by decide)
  have hprep' : (RowArithmetic.rowCount R+1)*(preparationSize M L R P Q N Win Wout Wsetup H)^2≤
      C^3*ell^4096 := by
    apply hprep.trans
    calc
      _ = C^3*ell^4033 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ ep
  have hterm' : (RowArithmetic.rowCount R+1)^3*(Q+N+Wout+64)^243≤C^246*ell^4096 := by
    apply hterm.trans
    calc
      _ = C^246*ell^3987 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ et
  have hp' := Nat.mul_le_mul_left (2^222) hprep'
  have ht' := Nat.mul_le_mul_left tensorTimeCoefficient hterm'
  simpa only [componentCost,Nat.add_mul,Nat.mul_assoc] using Nat.add_le_add hp' ht'

#print axioms componentCost_polylog
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
