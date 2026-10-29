import Maxwell.Spectral.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# From the trial-space polynomial bound to the local band inequality

This module proves the spectral inference. Its inputs are the explicit
polynomial quadratic-form estimate on a two-dimensional trial space and
an inertia bound of at most two eigenvalues in the eligible positive band.
-/

namespace Maxwell.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The degree-two polynomial `(A-E I)(b I-A)`, as an endomorphism. -/
def edgePolynomialMap (A : H →ₗ[ℂ] H) (E b : ℝ) : H →ₗ[ℂ] H :=
  (A - (E : ℂ) • LinearMap.id).comp ((b : ℂ) • LinearMap.id - A)

variable [FiniteDimensional ℂ H]

/-- The polynomial is diagonal in the original operator's eigenbasis; no
sorting or identification of the polynomial's eigenvalue list is needed. -/
theorem edgePolynomialMap_diagonal {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (E b : ℝ) (x : H) (i : Fin (Module.finrank ℂ H)) :
    (hA.eigenvectorBasis rfl).repr (edgePolynomialMap A E b x) i =
      (((hA.eigenvalues rfl i - E) * (b - hA.eigenvalues rfl i) : ℝ) : ℂ) *
        (hA.eigenvectorBasis rfl).repr x i := by
  simp only [edgePolynomialMap, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    hA.eigenvectorBasis_apply_self_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- Positive polynomial values lie between the two roots, hence in `(0,b)`
when the lower root is nonnegative and strictly below the upper root. -/
theorem polynomial_positive_eligible (E b lam : ℝ) (hE : 0 ≤ E) (hEb : E < b)
    (hg : 0 < (lam - E) * (b - lam)) : 0 < lam ∧ lam < b := by
  rcases (mul_pos_iff.mp hg) with h | h
  · constructor <;> linarith [h.1, h.2]
  · exfalso
    linarith [h.1, h.2]

/-- The final strict scalar gap uses the upper bound `b=7/256` on the
positive band, preserving the actual rational margin over `1/600`. -/
theorem polynomial_margin_implies_band_gap (r E lam : ℝ) (hr : 0 < r)
    (hlam : 0 < lam) (hlamb : lam < 7 / 256)
    (hg : r ^ 2 / 20450 ≤ (lam - E) * (7 / 256 - lam)) :
    r ^ 2 / 600 < lam - E := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hleft : 0 < lam - E := by
    have hprod : 0 < (lam - E) * (7 / 256 - lam) := by linarith
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr hlamb)).mp hprod
  have hmul := mul_lt_mul_of_pos_left hlam hleft
  nlinarith only [hg, hmul, hr2]

/-- The two-dimensional trial bound, together with the inertia count,
forces the quadratic lower bound for every eigenvalue in the positive band. -/
theorem local_band_gap {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (E r : ℝ) (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hr : 0 < r)
    (hinertia : (Finset.univ.filter fun i =>
      0 < hA.eigenvalues rfl i ∧ hA.eigenvalues rfl i < 7 / 256).card ≤ 2)
    (W : Submodule ℂ H) (hdim : 2 ≤ Module.finrank ℂ W)
    (htrial : ∀ x : W, (r ^ 2 / 20450) * ‖(x : H)‖ ^ 2 ≤
      Complex.re (inner ℂ (x : H) (edgePolynomialMap A E (7 / 256) x))) :
    ∀ i : Fin (Module.finrank ℂ H),
      0 < hA.eigenvalues rfl i → hA.eigenvalues rfl i < 7 / 256 →
      r ^ 2 / 600 < hA.eigenvalues rfl i - E := by
  classical
  let μ := fun i => (hA.eigenvalues rfl i - E) * (7 / 256 - hA.eigenvalues rfl i)
  let eligible := Finset.univ.filter fun i =>
    0 < hA.eigenvalues rfl i ∧ hA.eigenvalues rfl i < 7 / 256
  have hquad := diagonal_quadratic_form (hA.eigenvectorBasis rfl) μ
    (edgePolynomialMap_diagonal hA E (7 / 256))
  have hsub : ∀ i, r ^ 2 / 20450 ≤ μ i → i ∈ eligible := by
    intro i hi
    have hg : 0 < μ i := lt_of_lt_of_le (by positivity) hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      polynomial_positive_eligible E (7 / 256) (hA.eigenvalues rfl i)
        (by linarith) (by linarith) hg⟩
  have hall := quadratic_minmax_saturates (hA.eigenvectorBasis rfl) μ hquad W
    (r ^ 2 / 20450) eligible 2 htrial hsub hinertia hdim
  intro i hi hib
  exact polynomial_margin_implies_band_gap r E (hA.eigenvalues rfl i) hr hi hib
    (hall i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hib⟩))


section TrialMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

omit [FiniteDimensional ℂ H] in
/-- A strictly positive trial quadratic form already proves injectivity;
no independent rank or kernel premise is required. -/
theorem trial_map_injective (T : H →ₗ[ℂ] H) (F : V →ₗ[ℂ] H)
    (c : ℝ) (hc : 0 < c)
    (htrial : ∀ x : V, c * ‖x‖ ^ 2 ≤ Complex.re (inner ℂ (F x) (T (F x)))) :
    Function.Injective F := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h := htrial x
  simp only [hx, map_zero, inner_zero_left, Complex.zero_re] at h
  have hn : ‖x‖ ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right h hc) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

omit [FiniteDimensional ℂ H] in
/-- The Gram upper bound normalizes the manuscript's `r²/20000` estimate to
`r²/20450` on the actual range of the trial map. -/
theorem trial_range_quadratic_lower (T : H →ₗ[ℂ] H) (F : V →ₗ[ℂ] H) (r : ℝ)
    (htrial : ∀ x : V, (r ^ 2 / 20000) * ‖x‖ ^ 2 ≤
      Complex.re (inner ℂ (F x) (T (F x))))
    (hgram : ∀ x : V, ‖F x‖ ^ 2 ≤ (409 / 400) * ‖x‖ ^ 2) :
    ∀ y : LinearMap.range F, (r ^ 2 / 20450) * ‖(y : H)‖ ^ 2 ≤
      Complex.re (inner ℂ (y : H) (T y)) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.property
  have hg := mul_le_mul_of_nonneg_left (hgram x)
    (by positivity : 0 ≤ r ^ 2 / 20450)
  have h := htrial x
  rw [hx] at h hg
  nlinarith only [h, hg]

omit [FiniteDimensional ℂ H] in
/-- The geometric alternative: an isometric center map minus an orthogonal
corrector is injective, independently of the polynomial estimate. -/
theorem corrected_trial_injective (Phi : V →ₗᵢ[ℂ] H) (Y : V →ₗ[ℂ] H)
    (horth : ∀ x : V, inner ℂ (Phi x) (Y x) = 0) :
    Function.Injective (Phi.toLinearMap - Y) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hxy : Phi x = Y x := sub_eq_zero.mp hx
  have h := horth x
  rw [← hxy] at h
  have hz : Phi x = 0 := (inner_self_eq_zero.mp h)
  exact Phi.injective (hz.trans Phi.map_zero.symm)

/-- Local spectral separation from the finite Gram premises on the trial map.
The lower quadratic estimate implies the map has full trial-space rank, while
the upper Gram estimate supplies the normalization required by min-max. -/
theorem local_band_gap_of_trial_map [FiniteDimensional ℂ V]
    {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    (E r : ℝ) (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hr : 0 < r)
    (hinertia : (Finset.univ.filter fun i =>
      0 < hA.eigenvalues rfl i ∧ hA.eigenvalues rfl i < 7 / 256).card ≤ 2)
    (F : V →ₗ[ℂ] H) (hdim : 2 ≤ Module.finrank ℂ V)
    (htrial : ∀ x : V, (r ^ 2 / 20000) * ‖x‖ ^ 2 ≤
      Complex.re (inner ℂ (F x) (edgePolynomialMap A E (7 / 256) (F x))))
    (hgram : ∀ x : V, ‖F x‖ ^ 2 ≤ (409 / 400) * ‖x‖ ^ 2) :
    ∀ i : Fin (Module.finrank ℂ H),
      0 < hA.eigenvalues rfl i → hA.eigenvalues rfl i < 7 / 256 →
      r ^ 2 / 600 < hA.eigenvalues rfl i - E := by
  have hf := trial_map_injective (edgePolynomialMap A E (7 / 256)) F
    (r ^ 2 / 20000) (by positivity) htrial
  have hrank : 2 ≤ Module.finrank ℂ (LinearMap.range F) := by
    rw [LinearMap.finrank_range_of_inj hf]
    exact hdim
  exact local_band_gap hA E r hElo hEhi hr hinertia (LinearMap.range F) hrank
    (trial_range_quadratic_lower (edgePolynomialMap A E (7 / 256)) F r htrial hgram)

end TrialMap

end Maxwell.Spectral
