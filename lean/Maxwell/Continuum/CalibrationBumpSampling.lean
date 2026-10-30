import Maxwell.Continuum.CalibrationBumpDFT
import Maxwell.Continuum.CalibrationBumpPrecision
import Maxwell.Continuum.PeriodicSamplingTruncation

/-! Certified approximation of the actual well-root coefficients by
the finite rational DFT, including every omitted sampling alias. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open PeriodicSampling UnitAddTorus MasterConstants

attribute [local irreducible] rootTorus

theorem rootTorus_sample_error (grid D R : ℕ) [NeZero grid] (s : ℝ) (hs : 4 ≤ s)
    (n : Fin 3 → ℤ) (hn : n ∈ Product.frequencyCube D) (hgrid : D+R ≤ grid) :
    ‖Product.coefficient grid
      (fun j => rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle)))
        (Product.frequency grid n)-mFourierCoeff (rootTorus s hs) n‖ ≤
      Product.cubeTail (mFourierCoeff (rootTorus s hs)) (R : ℤ) := by
  have hc := rootTorus_coefficients_summable s hs
  have he := Product.coefficient_samples_error_window grid (mFourierCoeff (rootTorus s hs))
    hc D n ((Product.mem_frequencyCube D n).mp hn)
  simp_rw [Product.synthesis_coefficients _ hc] at he
  exact he.trans (Product.cubeTail_mono _ hc (by omega : (R : ℤ) ≤ (grid : ℤ)-D))

theorem rationalRootCoefficient_full_error (grid D R N ell P : ℕ) [NeZero grid]
    (s : ℚ) (hs : 4 ≤ (s : ℝ)) (n : Fin 3 → ℤ) (hn : n ∈ Product.frequencyCube D)
    (hgrid : D+R ≤ grid) (hR0 : 0 < R) (hlog : (s : ℝ) ≤ (2 : ℝ)^ell)
    (hR : Cs^2*(s : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2 ≤ (R : ℝ)) :
    ‖mFourierCoeff (rootTorus s hs) n-rectangleCenter (rationalRootCoefficient grid s P n)‖ ≤
      (1/2 : ℝ)^(N+8)+8*(1/2 : ℝ)^P := by
  have ha := (rootTorus_sample_error grid D R s hs n hn hgrid).trans
    (rootTorus_tail_requested s hs N ell R hR0 hlog hR)
  have hr := rationalRootCoefficient_error grid s hs P n
  have ht := norm_sub_le_norm_sub_add_norm_sub (mFourierCoeff (rootTorus s hs) n)
    (Product.coefficient grid
      (fun j => rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle)))
        (Product.frequency grid n)) (rectangleCenter (rationalRootCoefficient grid s P n))
  rw [norm_sub_rev (mFourierCoeff _ _) (Product.coefficient _ _ _)] at ht
  linarith

def rationalRootPolynomial (grid D P : ℕ) [NeZero grid] (s : ℚ)
    (x : UnitAddTorus (Fin 3)) : ℂ :=
  Product.polynomial (fun n => rectangleCenter (rationalRootCoefficient grid s P n)) D x

theorem rationalRootPolynomial_error (grid D R N ell P : ℕ) [NeZero grid]
    (s : ℚ) (hs : 4 ≤ (s : ℝ))
    (hgrid : D+R ≤ grid) (hR0 : 0 < R) (hRD : R ≤ D+1)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell)
    (hR : Cs^2*(s : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2 ≤ (R : ℝ))
    (x : UnitAddTorus (Fin 3)) :
    ‖rootTorus s hs x-rationalRootPolynomial grid D P s x‖ ≤
      (1/2 : ℝ)^(N+8)+((2*D+1 : ℕ) : ℝ)^3*((1/2 : ℝ)^(N+8)+8*(1/2 : ℝ)^P) := by
  have hc := rootTorus_coefficients_summable s hs
  have ht := (Product.polynomial_error _ hc D x).trans
    ((Product.cubeTail_mono _ hc (by exact_mod_cast hRD)).trans
      (rootTorus_tail_requested s hs N ell R hR0 hlog hR))
  have hr := Product.polynomial_rounding_error (mFourierCoeff (rootTorus s hs))
    (fun n => rectangleCenter (rationalRootCoefficient grid s P n)) D
    ((1/2 : ℝ)^(N+8)+8*(1/2 : ℝ)^P)
    (fun n hn => rationalRootCoefficient_full_error grid D R N ell P s hs n hn hgrid hR0 hlog hR) x
  rw [Product.frequencyCube_card, Nat.cast_pow] at hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ (Product.polynomial (mFourierCoeff (rootTorus s hs)) D x) _).trans
    (add_le_add ht hr)

#print axioms rationalRootCoefficient_full_error
#print axioms rationalRootPolynomial_error

end Maxwell.Continuum.Calibration
