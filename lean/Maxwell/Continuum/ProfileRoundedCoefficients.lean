import Maxwell.Continuum.ProfileDFT
import Maxwell.Continuum.ProfileCosineSeries
import Maxwell.Continuum.DyadicRounding

/-! The finite coefficient encoder and its accumulated precision budget. -/

namespace Maxwell.Continuum.Profile

def sampledCosineCoefficient (grid D P : ℕ) [NeZero grid] (j : ℕ) : ℚ :=
  if j=0 then rationalSampleCoefficient grid D P 0
  else rationalSampleCoefficient grid D P (j : ℤ)+rationalSampleCoefficient grid D P (-(j : ℤ))

theorem sampledCosineCoefficient_error (grid D P j : ℕ) [NeZero grid]
    (hj : j ≤ D) (hgrid : profileDegree P+D ≤ grid) :
    |cosineCoefficient j-(sampledCosineCoefficient grid D P j : ℝ)| ≤ 8*(1/2 : ℝ)^P := by
  have hp := rationalSampleCoefficient_full_error grid D P (j : ℤ)
    (by simpa only [Int.abs_natCast, Int.ofNat_le] using hj) hgrid
  have hm := rationalSampleCoefficient_full_error grid D P (-(j : ℤ))
    (by simpa only [abs_neg, Int.abs_natCast, Int.ofNat_le] using hj) hgrid
  by_cases hz : j=0
  · subst j
    simp only [cosineCoefficient, sampledCosineCoefficient, ↓reduceIte, Int.natCast_zero] at hp ⊢
    linarith [pow_pos (by norm_num : (0 : ℝ)<1/2) P]
  · simp only [cosineCoefficient, sampledCosineCoefficient, hz, ↓reduceIte, Rat.cast_add]
    calc
      _ = |((angularCoefficient 0 (j : ℤ)).re-(rationalSampleCoefficient grid D P (j : ℤ) : ℝ))+
        ((angularCoefficient 0 (-(j : ℤ))).re-(rationalSampleCoefficient grid D P (-(j : ℤ)) : ℝ))| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)

instance profileGrid_neZero (N : ℕ) : NeZero (profileGrid N) := ⟨(profileGrid_pos N).ne'⟩

def roundedCoefficient (N j : ℕ) : Dyadic (profileWorkBits N) :=
  roundDyadic (profileWorkBits N)
    (sampledCosineCoefficient (profileGrid N) (profileDegree N) (profileWorkBits N) j)

theorem roundedCoefficient_error (N j : ℕ) (hj : j ≤ profileDegree N) :
    |cosineCoefficient j-((roundedCoefficient N j).value : ℝ)| ≤
      9*(1/2 : ℝ)^profileWorkBits N := by
  have hs := sampledCosineCoefficient_error (profileGrid N) (profileDegree N)
    (profileWorkBits N) j hj (by unfold profileGrid; omega)
  have hr := roundDyadic_error (profileWorkBits N)
    (sampledCosineCoefficient (profileGrid N) (profileDegree N) (profileWorkBits N) j)
  change |(sampledCosineCoefficient (profileGrid N) (profileDegree N) (profileWorkBits N) j : ℝ)-
    ((roundedCoefficient N j).value : ℝ)| ≤ _ at hr
  exact (abs_sub_le (cosineCoefficient j)
    (sampledCosineCoefficient (profileGrid N) (profileDegree N) (profileWorkBits N) j : ℝ)
    ((roundedCoefficient N j).value : ℝ)).trans (by linarith)

theorem roundedCoefficient_bound (N j : ℕ) (hj : j ≤ profileDegree N) :
    |(roundedCoefficient N j).value| ≤ (57 : ℚ) := by
  have he := roundedCoefficient_error N j hj
  have hc := cosineCoefficient_decay j
  have hex : Real.exp (-Real.sqrt (j : ℝ)/64) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Real.sqrt_nonneg (j : ℝ)])
  have hp : (1/2 : ℝ)^profileWorkBits N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le ((roundedCoefficient N j).value : ℝ) (cosineCoefficient j) 0
  simp only [sub_zero, abs_sub_comm _ (cosineCoefficient j)] at ht
  have hb : |((roundedCoefficient N j).value : ℝ)| ≤ 57 := by linarith
  exact_mod_cast hb

theorem profileWorkBits_error (N : ℕ) :
    18*((profileDegree N : ℝ)+1)^3*(1/2 : ℝ)^profileWorkBits N ≤
      (1/2 : ℝ)^(N+27) := by
  have hD : (profileDegree N : ℝ)+1 ≤ (2 : ℝ)^Nat.clog 2 (profileDegree N+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (profileDegree N+1)
  calc
    _ ≤ 18*((2 : ℝ)^Nat.clog 2 (profileDegree N+1))^3*(1/2 : ℝ)^profileWorkBits N := by gcongr
    _ = 18*(1/2 : ℝ)^(N+32) := by
      unfold profileWorkBits
      rw [pow_add, pow_add, ← pow_mul]
      have he : ((2 : ℝ)^Nat.clog 2 (profileDegree N+1))^3*
          (1/2 : ℝ)^(3*Nat.clog 2 (profileDegree N+1))=1 := by
        rw [← pow_mul, Nat.mul_comm, ← mul_pow]
        norm_num
      rw [pow_add]
      calc
        _ = 18*((1/2 : ℝ)^N*(1/2 : ℝ)^32)*
          (((2 : ℝ)^Nat.clog 2 (profileDegree N+1))^3*
          (1/2 : ℝ)^(3*Nat.clog 2 (profileDegree N+1))) := by ring
        _ = _ := by rw [he, mul_one]
    _ ≤ _ := by
      rw [show N+32=(N+27)+5 by omega, pow_add]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (N+27)]

#print axioms roundedCoefficient_error
#print axioms profileWorkBits_error

end Maxwell.Continuum.Profile
