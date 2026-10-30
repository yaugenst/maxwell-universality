import Maxwell.Continuum.CutoffEvaluation
import Maxwell.Continuum.TensorChebyshev

/-! Finite rational enclosures of the literal three-dimensional Bloch cutoff,
including errors in its normalized input coordinates. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate Well

def chiCenter (q : Fin 3 → ℚ) (N : ℕ) : ℚ := ∏ i, psiCenter (q i) N

attribute [local irreducible] psiCenter chiCenter

theorem chiCenter_error (q : Fin 3 → ℚ) (N : ℕ) (x : Fin 3 → ℝ)
    {η : ℝ} (hη : 0≤η) (hx : ∀ i, |x i-(q i : ℝ)|≤η) :
    |(∏ i, psi (x i))-(chiCenter q N : ℝ)|≤112*η+7*(1/2 : ℝ)^(N+19) := by
  have he (i : Fin 3) : |psi (x i)-(psiCenter (q i) N : ℝ)|≤16*η+(1/2 : ℝ)^(N+19) := by
    have hl := psi_lipschitz.dist_le_mul (x i) (q i : ℝ)
    simp only [Real.dist_eq,NNReal.coe_ofNat] at hl
    exact (abs_sub_le (psi (x i)) (psi (q i : ℝ)) (psiCenter (q i) N : ℝ)).trans
      (add_le_add (hl.trans (mul_le_mul_of_nonneg_left (hx i) (by norm_num)))
        (psiCenter_error (q i) N))
  have hp := Profile.triple_product_error
    (fun i => (psi (x i) : ℂ)) (fun i => ((psiCenter (q i) N : ℝ) : ℂ))
    (by positivity : 0≤16*η+(1/2 : ℝ)^(N+19))
    (fun i => by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (psi_nonneg _)] using psi_le_one (x i))
    (fun i => by
      simp only [Complex.norm_real,Real.norm_eq_abs]
      have hb := (Rat.cast_le (K := ℝ)).mpr (psiCenter_bound (q i) N)
      simpa only [Rat.cast_abs,Rat.cast_ofNat] using hb)
    (fun i => by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using he i)
  rw [← Complex.ofReal_prod,← Complex.ofReal_prod,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at hp
  have heq : 7*(16*η+(1/2 : ℝ)^(N+19))=112*η+7*(1/2 : ℝ)^(N+19) := by ring
  rw [heq] at hp
  simpa only [chiCenter,Rat.cast_prod] using hp

def chiApprox (q : Fin 3 → ℚ) (P : ℕ) : Ball := ⟨chiCenter q P,(1/2)^P,by positivity⟩

theorem chiApprox_contains (q : Fin 3 → ℚ) (P : ℕ) (q₀ : ℝ) (x : Space)
    (hx : ∀ i, |x i/q₀-(q i : ℝ)|≤(1/2 : ℝ)^(P+12)) :
    (chiApprox q P).Contains (chi q₀ x) := by
  have h := chiCenter_error q P (fun i => x i/q₀) (by positivity) hx
  change |(∏ i, psi (x i/q₀))-(chiCenter q P : ℝ)|≤(((1/2 : ℚ)^P : ℚ) : ℝ)
  push_cast
  apply h.trans
  rw [pow_add,pow_add]
  nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) P]

theorem chiCenter_bound (q : Fin 3 → ℚ) (P : ℕ) : |chiCenter q P|≤8 := by
  rw [chiCenter,Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin 3, (2 : ℚ) := Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      (fun i _ => psiCenter_bound (q i) P)
    _ = _ := by norm_num

#print axioms chiApprox_contains

end Maxwell.Continuum.Calibration
