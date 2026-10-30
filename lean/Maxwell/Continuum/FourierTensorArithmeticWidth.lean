import Maxwell.Continuum.FourierTensorModeCompleteComponent
import Maxwell.Continuum.CalibrationCompactModeWords

/-! A literal, computed small workspace bound for tensor arithmetic.
It depends on rounded coefficient precision and logarithmic dimensions,
not the unreduced calibration-array entry width. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
open Maxwell.Cost RationalDataflow Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def inputWidth (M A L : ℕ) : ℕ := lengthBits M+lengthBits A+lengthBits L+1

def arithmeticWidth (M A L R P Q N E : ℕ) : ℕ :=
  factorWidth A (inputWidth M A L)+P+3*waveWorkBits (8*Q) N+E+32+
    lengthBits R+lengthBits (aliasArraySize R)+lengthBits (RowArithmetic.rowCount R)+
    lengthBits Q+lengthBits N+lengthBits (waveDegree (8*Q) N)+lengthBits (waveGrid (8*Q) N)

theorem lengthBits_eq (n : ℕ) : lengthBits n=n.bits.length := PhaseMachine.Runtime.clog_two_succ n

theorem inputWidth_spec (M A L : ℕ) :
    1≤ inputWidth M A L ∧ M.bits.length≤ inputWidth M A L ∧
      A.bits.length≤ inputWidth M A L ∧ L.bits.length≤ inputWidth M A L := by
  simp only [inputWidth,lengthBits_eq]
  omega

theorem arithmeticWidth_spec (M A L R P Q N E : ℕ) :
    factorWidth A (inputWidth M A L)≤arithmeticWidth M A L R P Q N E ∧
      6≤arithmeticWidth M A L R P Q N E ∧
      R.bits.length≤arithmeticWidth M A L R P Q N E ∧
      (aliasArraySize R).bits.length≤arithmeticWidth M A L R P Q N E ∧
      (RowArithmetic.rowCount R).bits.length≤arithmeticWidth M A L R P Q N E ∧
      P+3*waveWorkBits (8*Q) N+E+16≤arithmeticWidth M A L R P Q N E ∧
      Q.bits.length≤arithmeticWidth M A L R P Q N E ∧
      N.bits.length≤arithmeticWidth M A L R P Q N E ∧
      (waveDegree (8*Q) N).bits.length≤arithmeticWidth M A L R P Q N E ∧
      waveWorkBits (8*Q) N+7≤arithmeticWidth M A L R P Q N E ∧
      (waveGrid (8*Q) N).bits.length≤arithmeticWidth M A L R P Q N E := by
  simp only [arithmeticWidth,lengthBits_eq]
  omega

def logCoefficient (C : ℕ) : ℕ := Nat.clog 2 (C+1)+33
def arithmeticCoefficient (C : ℕ) : ℕ :=
  103*logCoefficient C+18*C+3*wavePrecisionCoefficient C+128

theorem arithmeticWidth_linear {M A L R P Q N E C ell : ℕ} (hell : 0<ell)
    (hm : M≤C*ell^33) (ha : A≤C*ell) (hl : L≤C*ell^33)
    (hr : R≤C*ell^33) (hc : aliasArraySize R≤C*ell^33)
    (hn : RowArithmetic.rowCount R≤C*ell^33)
    (hp : P≤C*ell) (hq : Q≤C*ell^8) (hnt : N≤C*ell) (he : E≤C*ell)
    (hd : waveDegree (8*Q) N≤C*ell^33) (hg : waveGrid (8*Q) N≤C*ell^33) :
    arithmeticWidth M A L R P Q N E≤arithmeticCoefficient C*ell := by
  have e133 : ell≤ell^33 := Nat.le_self_pow (by decide) ell
  have e833 : ell^8≤ell^33 := Nat.pow_le_pow_right hell (by decide)
  have la := FiniteAlgorithm.lengthBits_polynomial hell 33
    (ha.trans (Nat.mul_le_mul_left C e133))
  have lm := FiniteAlgorithm.lengthBits_polynomial hell 33 hm
  have ll := FiniteAlgorithm.lengthBits_polynomial hell 33 hl
  have lr := FiniteAlgorithm.lengthBits_polynomial hell 33 hr
  have lc := FiniteAlgorithm.lengthBits_polynomial hell 33 hc
  have ln := FiniteAlgorithm.lengthBits_polynomial hell 33 hn
  have lq := FiniteAlgorithm.lengthBits_polynomial hell 33
    (hq.trans (Nat.mul_le_mul_left C e833))
  have lnt := FiniteAlgorithm.lengthBits_polynomial hell 33
    (hnt.trans (Nat.mul_le_mul_left C e133))
  have ld := FiniteAlgorithm.lengthBits_polynomial hell 33 hd
  have lg := FiniteAlgorithm.lengthBits_polynomial hell 33 hg
  have hw := waveWorkBits_polylog hell hq hnt
  unfold arithmeticWidth factorWidth inputWidth arithmeticCoefficient logCoefficient
  nlinarith only [la,lm,ll,lr,lc,ln,lq,lnt,ld,lg,ha,hp,he,hw,hell]

theorem rowCount_polynomial {R C ell : ℕ} (hell : 0<ell) (hr : R≤C*ell^11) :
    RowArithmetic.rowCount R≤(2*C+1)^3*ell^33 := by
  have h1 : 1≤ell^11 := one_le_pow₀ hell
  have hs : 2*R+1≤(2*C+1)*ell^11 := by nlinarith only [hr,h1]
  have h := Nat.pow_le_pow_left hs 3
  calc
    _ = (2*R+1)^3 := by unfold RowArithmetic.rowCount aliasSide;ring
    _ ≤ ((2*C+1)*ell^11)^3 := h
    _ = _ := by ring

theorem aliasArraySize_polynomial {R C ell : ℕ} (hell : 0<ell) (hr : R≤C*ell^11) :
    aliasArraySize R≤3*(2*C+1)^3*ell^33 := by
  have h := Nat.mul_le_mul_left 3 (rowCount_polynomial hell hr)
  simpa only [aliasArraySize,RowArithmetic.rowCount,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem row_mass (R : ℕ) : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^Supercell.compactMassBits (lengthBits (2*R+1)) := by
  have h := lengthBits_bound (2*R+1)
  push_cast at h
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*R+1) h 3
  have h6 : (6:ℝ)≤2^5 := by norm_num
  have hm := mul_le_mul h6 hpow (by positivity) (by positivity)
  convert hm using 1
  · simp only [RowArithmetic.rowCount,aliasSide,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  · rw [Supercell.compactMassBits,pow_add,←pow_mul]
    ring

#print axioms arithmeticWidth_linear
#print axioms row_mass
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
