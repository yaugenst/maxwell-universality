import Maxwell.Continuum.ChebyshevWaveDFT
import Maxwell.Continuum.ComplexDyadic
import Mathlib.Data.Nat.Log

/-! Actual dyadic plane-wave coefficients and their logarithmic guard precision. -/

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate Calibration

theorem rectangleCenter_add (a b : ComplexRectangle) :
    rectangleCenter (a.add b)=rectangleCenter a+rectangleCenter b := by
  simp only [rectangleCenter, ComplexRectangle.add, Ball.add]
  push_cast
  ring

def rationalWaveCosineCoefficient (grid : ℕ) [NeZero grid] (q : ℚ) (Q P j : ℕ) :
    ComplexRectangle :=
  if j=0 then rationalWaveCoefficient grid q Q P 0
  else (rationalWaveCoefficient grid q Q P (j : ℤ)).add
    (rationalWaveCoefficient grid q Q P (-(j : ℤ)))

theorem rationalWaveCosineCoefficient_error (grid D K P : ℕ) [NeZero grid]
    (q : ℚ) (Q j : ℕ) (hq : |q|≤Q) (hk : |2*Real.pi*(q : ℝ)|≤K)
    (hj : j≤D) (hgrid : waveDegree K P+D≤grid) :
    ‖waveCosineCoefficient (2*Real.pi*(q : ℝ)) j-
      rectangleCenter (rationalWaveCosineCoefficient grid q Q P j)‖ ≤ 18*(1/2 : ℝ)^P := by
  have hp := rationalWaveCoefficient_full_error grid D K P q Q hq hk (j : ℤ)
    (by simpa only [Int.abs_natCast, Int.ofNat_le] using hj) hgrid
  have hm := rationalWaveCoefficient_full_error grid D K P q Q hq hk (-(j : ℤ))
    (by simpa only [abs_neg, Int.abs_natCast, Int.ofNat_le] using hj) hgrid
  by_cases hz : j=0
  · subst j
    simp only [waveCosineCoefficient, rationalWaveCosineCoefficient, ↓reduceIte, Int.natCast_zero] at hp ⊢
    linarith [pow_pos (by norm_num : (0 : ℝ)<1/2) P]
  · simp only [waveCosineCoefficient, rationalWaveCosineCoefficient, hz, ↓reduceIte, rectangleCenter_add]
    calc
      _ = ‖(waveCoefficient (2*Real.pi*(q : ℝ)) (j : ℤ)-
          rectangleCenter (rationalWaveCoefficient grid q Q P (j : ℤ)))+
        (waveCoefficient (2*Real.pi*(q : ℝ)) (-(j : ℤ))-
          rectangleCenter (rationalWaveCoefficient grid q Q P (-(j : ℤ))))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (by linarith)

def waveWorkBits (K N : ℕ) : ℕ := N+Nat.clog 2 (waveDegree K N+1)+32
def waveGrid (K N : ℕ) : ℕ := waveDegree K N+waveDegree K (waveWorkBits K N)+1

instance waveGrid_neZero (K N : ℕ) : NeZero (waveGrid K N) := by
  constructor
  unfold waveGrid
  omega

theorem waveFrequency_bound (q : ℚ) (Q : ℕ) (hq : |q|≤Q) :
    |2*Real.pi*(q : ℝ)|≤(8*Q : ℕ) := by
  have hqr : |(q : ℝ)|≤Q := by exact_mod_cast hq
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  push_cast
  calc
    _ ≤ (2*Real.pi)*(Q : ℝ) := mul_le_mul_of_nonneg_left hqr (by positivity)
    _ ≤ _ := by nlinarith only [Real.pi_lt_four, Nat.cast_nonneg Q (α := ℝ)]

def waveRoundedCoefficient (q : ℚ) (Q N j : ℕ) : ComplexDyadic (waveWorkBits (8*Q) N) :=
  roundComplex (waveWorkBits (8*Q) N)
    (rationalWaveCosineCoefficient (waveGrid (8*Q) N) q Q (waveWorkBits (8*Q) N) j)

theorem waveRoundedCoefficient_error (q : ℚ) (Q N j : ℕ)
    (hq : |q|≤Q) (hj : j≤waveDegree (8*Q) N) :
    ‖waveCosineCoefficient (2*Real.pi*(q : ℝ)) j-
      complexDyadicValue (waveRoundedCoefficient q Q N j)‖ ≤ 20*(1/2 : ℝ)^waveWorkBits (8*Q) N := by
  have hs := rationalWaveCosineCoefficient_error (waveGrid (8*Q) N) (waveDegree (8*Q) N)
    (8*Q) (waveWorkBits (8*Q) N) q Q j hq (waveFrequency_bound q Q hq) hj
    (by unfold waveGrid; omega)
  have hr := roundComplex_error (waveWorkBits (8*Q) N)
    (rationalWaveCosineCoefficient (waveGrid (8*Q) N) q Q (waveWorkBits (8*Q) N) j)
  change ‖_-complexDyadicValue (waveRoundedCoefficient q Q N j)‖≤_ at hr
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (rectangleCenter (rationalWaveCosineCoefficient (waveGrid (8*Q) N) q Q (waveWorkBits (8*Q) N) j)) _).trans
    (by linarith)

theorem waveRoundedCoefficient_bound (q : ℚ) (Q N j : ℕ)
    (hq : |q|≤Q) (hj : j≤waveDegree (8*Q) N) :
    ‖complexDyadicValue (waveRoundedCoefficient q Q N j)‖≤22 := by
  have he := waveRoundedCoefficient_error q Q N j hq hj
  have hc := waveCosineCoefficient_bound (2*Real.pi*(q : ℝ)) j
  have hp : (1/2 : ℝ)^waveWorkBits (8*Q) N≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (complexDyadicValue (waveRoundedCoefficient q Q N j)) (waveCosineCoefficient (2*Real.pi*(q : ℝ)) j) 0
  simp only [sub_zero] at ht
  rw [norm_sub_rev (complexDyadicValue _) _] at ht
  linarith

theorem waveWorkBits_error (K N : ℕ) :
    20*((waveDegree K N : ℝ)+1)*(1/2 : ℝ)^waveWorkBits K N≤(1/2 : ℝ)^(N+27) := by
  have hD : (waveDegree K N : ℝ)+1≤(2 : ℝ)^Nat.clog 2 (waveDegree K N+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (waveDegree K N+1)
  calc
    _ ≤ 20*(2 : ℝ)^Nat.clog 2 (waveDegree K N+1)*(1/2 : ℝ)^waveWorkBits K N := by gcongr
    _ = 20*(1/2 : ℝ)^(N+32) := by
      unfold waveWorkBits
      rw [pow_add, pow_add]
      have hc : (2 : ℝ)^Nat.clog 2 (waveDegree K N+1)*(1/2 : ℝ)^Nat.clog 2 (waveDegree K N+1)=1 := by
        rw [← mul_pow]
        norm_num
      rw [pow_add]
      calc
        _ = 20*((1/2 : ℝ)^N*(1/2 : ℝ)^32)*
          ((2 : ℝ)^Nat.clog 2 (waveDegree K N+1)*(1/2 : ℝ)^Nat.clog 2 (waveDegree K N+1)) := by ring
        _ = _ := by rw [hc, mul_one]
    _ ≤ _ := by
      rw [show N+32=(N+27)+5 by omega, pow_add]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) (N+27)]

#print axioms waveRoundedCoefficient_error
#print axioms waveRoundedCoefficient_bound

end Maxwell.Continuum.Profile
