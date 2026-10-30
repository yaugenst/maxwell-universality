import Maxwell.Continuum.ProfileCosineSeries
import Maxwell.Continuum.ProfileChebyshevBasis
import Maxwell.Continuum.SeriesTruncation
import Mathlib.Analysis.Calculus.SmoothSeries

/-! The literal Chebyshev series converges with its derivative on the closed profile interval. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Filter
open scoped Topology

def coefficientWeight (j : ℕ) : ℝ := (1+(j : ℝ)^2)*|cosineCoefficient j|

theorem coefficientWeight_summable : Summable coefficientWeight := cosineCoefficient_weighted_summable

theorem coefficientWeight_nonneg (j : ℕ) : 0 ≤ coefficientWeight j := by unfold coefficientWeight; positivity

theorem coefficient_le_weight (j : ℕ) : |cosineCoefficient j| ≤ coefficientWeight j := by
  unfold coefficientWeight
  nlinarith only [mul_nonneg (sq_nonneg (j : ℝ)) (abs_nonneg (cosineCoefficient j))]

theorem basis_term_bound (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖cosineCoefficient j*basis j t‖ ≤ coefficientWeight j := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (basis_bound j ht) (abs_nonneg _)).trans
    (by simpa only [mul_one] using coefficient_le_weight j)

theorem basis_derivative_term_bound (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖cosineCoefficient j*basisDerivative j t‖ ≤ 2*coefficientWeight j := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left (basisDerivative_bound j ht) (abs_nonneg _)).trans
  unfold coefficientWeight
  nlinarith only [abs_nonneg (cosineCoefficient j)]

theorem radial_hasSum {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun j : ℕ => cosineCoefficient j*basis j t) (radial t) := by
  let φ := Real.arccos (2*t-1)
  have hc : Real.cos φ = 2*t-1 := Real.cos_arccos (by linarith [ht.1]) (by linarith [ht.2])
  have he : (1+Real.cos φ)/2 = t := by rw [hc]; ring
  have h := cosineCoefficient_hasSum φ
  rw [angular_eq_radial, he] at h
  convert h using 1
  funext j
  rw [← basis_cosine, he]

theorem radial_series_derivative_open {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv radial t = ∑' j : ℕ, cosineCoefficient j*basisDerivative j t := by
  have hd := hasDerivAt_tsum_of_isPreconnected (coefficientWeight_summable.mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun j x (_ : x ∈ Ioo (0 : ℝ) 1) => (basis_hasDerivAt j x).const_mul (cosineCoefficient j))
    (fun j x hx => basis_derivative_term_bound j (Ioo_subset_Icc_self hx))
    (show (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num)
    (radial_hasSum (show (1/2 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)).summable ht
  have he : radial =ᶠ[𝓝 t] (fun x => ∑' j : ℕ, cosineCoefficient j*basis j x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (radial_hasSum (Ioo_subset_Icc_self hx)).tsum_eq.symm
  exact (hd.congr_of_eventuallyEq he).deriv

theorem radial_series_derivative {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    deriv radial t = ∑' j : ℕ, cosineCoefficient j*basisDerivative j t := by
  have hc : ContinuousOn (fun x => ∑' j : ℕ, cosineCoefficient j*basisDerivative j x)
      (Icc (0 : ℝ) 1) := by
    apply continuousOn_tsum _ (coefficientWeight_summable.mul_left 2)
      (fun j x hx => basis_derivative_term_bound j hx)
    intro j
    have h : Continuous (fun x => cosineCoefficient j*basisDerivative j x) := by
      unfold basisDerivative
      fun_prop
    exact h.continuousOn
  have he : EqOn (deriv radial) (fun x => ∑' j : ℕ, cosineCoefficient j*basisDerivative j x)
      (Ioo (0 : ℝ) 1) := fun _ hx => radial_series_derivative_open hx
  apply he.of_subset_closure (radial_contDiff.continuous_deriv (by simp)).continuousOn
    hc Ioo_subset_Icc_self _ ht
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

def exactTruncation (D : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range D, cosineCoefficient j*basis j t

def exactTruncationDerivative (D : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range D, cosineCoefficient j*basisDerivative j t

theorem exactTruncation_hasDerivAt (D : ℕ) (t : ℝ) :
    HasDerivAt (exactTruncation D) (exactTruncationDerivative D t) t := by
  exact HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range D) =>
    (basis_hasDerivAt j t).const_mul (cosineCoefficient j))

theorem exactTruncation_error (D : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |radial t-exactTruncation D t| ≤ (2 : ℝ)^87*Real.exp (-Real.sqrt D/128) := by
  have h := series_truncation_norm (fun j => cosineCoefficient j*basis j t) coefficientWeight
    coefficientWeight_summable (fun j => basis_term_bound j ht) D
  rw [(radial_hasSum ht).tsum_eq, Real.norm_eq_abs] at h
  exact h.trans (cosineCoefficient_weighted_tail D)

theorem exactTruncation_derivative_error (D : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |deriv radial t-exactTruncationDerivative D t| ≤ (2 : ℝ)^88*Real.exp (-Real.sqrt D/128) := by
  have h := series_truncation_norm (fun j => cosineCoefficient j*basisDerivative j t)
    (fun j => 2*coefficientWeight j) (coefficientWeight_summable.mul_left 2)
    (fun j => basis_derivative_term_bound j ht) D
  rw [← radial_series_derivative ht, Real.norm_eq_abs] at h
  have he : (∑' j : ℕ, if D ≤ j then 2*coefficientWeight j else 0) =
      2*(∑' j : ℕ, if D ≤ j then coefficientWeight j else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    split_ifs <;> simp
  rw [he] at h
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (cosineCoefficient_weighted_tail D) (by norm_num : (0 : ℝ) ≤ 2)
  change 2*(∑' j : ℕ, if D ≤ j then coefficientWeight j else 0) ≤
    2*((2 : ℝ)^87*Real.exp (-Real.sqrt D/128)) at hb
  exact hb.trans_eq (by ring)

#print axioms radial_series_derivative
#print axioms exactTruncation_error
#print axioms exactTruncation_derivative_error

end Maxwell.Continuum.Profile
