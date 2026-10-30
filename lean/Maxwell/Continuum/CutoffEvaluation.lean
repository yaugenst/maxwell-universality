import Maxwell.Continuum.CutoffIntegralEvaluation
import Maxwell.Continuum.CutoffClippedIntegral
import Maxwell.Certificate.Interval

/-! Rational enclosures of the actual normalized convolution cutoff. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate Well

def cutoffClampRat (x : ℚ) : ℚ := max (-1/2) (min (1/2) x)

theorem cutoffClampRat_cast (x : ℚ) : (cutoffClampRat x : ℝ)=cutoffClamp (x : ℝ) := by
  simp only [cutoffClampRat,cutoffClamp,Rat.cast_max,Rat.cast_min,Rat.cast_neg,Rat.cast_div,
    Rat.cast_one,Rat.cast_ofNat]

theorem cutoffClampRat_bounds (x : ℚ) : -1/2≤cutoffClampRat x ∧ cutoffClampRat x≤1/2 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem cutoffClampRat_mono : Monotone cutoffClampRat := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_left _ hxy)

def cutoffDenominatorApprox (N : ℕ) : ℚ := cutoffIntegralApprox N (-1/2) (1/2)
def psiNumeratorApprox (x : ℚ) (N : ℕ) : ℚ :=
  cutoffIntegralApprox N (cutoffClampRat (x-3/2)) (cutoffClampRat (x+3/2))

attribute [local irreducible] cutoffDenominatorApprox psiNumeratorApprox

theorem cutoffDenominatorApprox_error (N : ℕ) :
    |cutoffNormalization-(cutoffDenominatorApprox N : ℝ)|≤(1/2 : ℝ)^(N+24) := by
  have h := cutoffIntegralApprox_error N (a := -1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  simpa only [cutoffDenominatorApprox,cutoffNormalization_eq_intervalIntegral] using h

theorem cutoffDenominatorApprox_lower (N : ℕ) : (1/16 : ℚ)≤cutoffDenominatorApprox N := by
  have he := cutoffDenominatorApprox_error N
  have hp : (1/2 : ℝ)^(N+24)≤1/16 := by
    calc
      _ ≤ (1/2 : ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have hn := cutoffNormalization_bounds.1
  have hl : (1/16 : ℝ)≤(cutoffDenominatorApprox N : ℝ) := by linarith [le_abs_self (cutoffNormalization-(cutoffDenominatorApprox N : ℝ))]
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hl

theorem psiNumeratorApprox_error (x : ℚ) (N : ℕ) :
    |psi (x : ℝ)*cutoffNormalization-(psiNumeratorApprox x N : ℝ)|≤(1/2 : ℝ)^(N+24) := by
  unfold psiNumeratorApprox
  have h := cutoffIntegralApprox_error N
    (cutoffClampRat_bounds (x-3/2)).1 (cutoffClampRat_bounds (x+3/2)).2
    (cutoffClampRat_mono (show x-3/2≤x+3/2 by linarith))
  simp only [cutoffClampRat_cast,Rat.cast_sub,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] at h
  have he := (eq_div_iff cutoffNormalization_pos.ne').mp (psi_eq_clipped_integral (x : ℝ))
  rw [he]
  exact h

def psiCenter (x : ℚ) (N : ℕ) : ℚ := psiNumeratorApprox x N/cutoffDenominatorApprox N

attribute [local irreducible] psiCenter

theorem psiCenter_error (x : ℚ) (N : ℕ) :
    |psi (x : ℝ)-(psiCenter x N : ℝ)|≤(1/2 : ℝ)^(N+19) := by
  have hn := psiNumeratorApprox_error x N
  have hd := cutoffDenominatorApprox_error N
  have hl : (1/16 : ℝ)≤(cutoffDenominatorApprox N : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (cutoffDenominatorApprox_lower N)
  have hpos : (0 : ℝ)<(cutoffDenominatorApprox N : ℝ) := by linarith
  have hψ : |psi (x : ℝ)|≤1 := by rw [abs_of_nonneg (psi_nonneg _)]; exact psi_le_one _
  have he : |psi (x : ℝ)*(cutoffDenominatorApprox N : ℝ)-(psiNumeratorApprox x N : ℝ)|≤
      2*(1/2 : ℝ)^(N+24) := by
    calc
      _ = |psi (x : ℝ)*((cutoffDenominatorApprox N : ℝ)-cutoffNormalization)+
        (psi (x : ℝ)*cutoffNormalization-(psiNumeratorApprox x N : ℝ))| := by congr 1; ring
      _ ≤ |psi (x : ℝ)| * |(cutoffDenominatorApprox N : ℝ)-cutoffNormalization|+
        |psi (x : ℝ)*cutoffNormalization-(psiNumeratorApprox x N : ℝ)| := by
          simpa only [abs_mul] using abs_add_le
            (psi (x : ℝ)*((cutoffDenominatorApprox N : ℝ)-cutoffNormalization))
            (psi (x : ℝ)*cutoffNormalization-(psiNumeratorApprox x N : ℝ))
      _ ≤ 1*(1/2 : ℝ)^(N+24)+(1/2 : ℝ)^(N+24) := add_le_add
        (mul_le_mul hψ (by simpa only [abs_sub_comm] using hd) (abs_nonneg _) zero_le_one) hn
      _ = _ := by ring
  have hquot : psi (x : ℝ)-(psiNumeratorApprox x N : ℝ)/(cutoffDenominatorApprox N : ℝ)=
      (psi (x : ℝ)*(cutoffDenominatorApprox N : ℝ)-(psiNumeratorApprox x N : ℝ))/(cutoffDenominatorApprox N : ℝ) := by
    field_simp
  rw [psiCenter,Rat.cast_div,hquot,abs_div,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have hb := mul_le_mul_of_nonneg_left hl (pow_nonneg (by norm_num : (0 : ℝ)≤1/2) (N+19))
  have heq : (1/2 : ℝ)^(N+19)*(1/16)=2*(1/2 : ℝ)^(N+24) := by
    rw [show N+24=(N+19)+5 by omega,pow_add]
    ring
  rw [heq] at hb
  exact he.trans hb

def psiApprox (x : ℚ) (P : ℕ) : Ball := ⟨psiCenter x P,(1/2)^P,by positivity⟩

theorem psiApprox_contains (x : ℚ) (P : ℕ) : (psiApprox x P).Contains (psi (x : ℝ)) := by
  have he := psiCenter_error x P
  change |psi (x : ℝ)-(psiCenter x P : ℝ)|≤(((1/2 : ℚ)^P : ℚ) : ℝ)
  push_cast
  exact he.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))

theorem psiCenter_bound (x : ℚ) (P : ℕ) : |psiCenter x P|≤2 := by
  have he := psiCenter_error x P
  have hp : (1/2 : ℝ)^(P+19)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le (psiCenter x P : ℝ) (psi (x : ℝ)) 0
  simp only [sub_zero,abs_sub_comm _ (psi _),abs_of_nonneg (psi_nonneg _)] at ht
  have hb : |(psiCenter x P : ℝ)|≤2 := by linarith [psi_le_one (x : ℝ)]
  exact_mod_cast hb

#print axioms psiCenter_error
#print axioms psiApprox_contains

end Maxwell.Continuum.Calibration
