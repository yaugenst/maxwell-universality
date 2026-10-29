import Maxwell.Defect.RationalCertificate
import Maxwell.Defect.RationalResidual
import Maxwell.Defect.CertificateCompleteness
import Maxwell.Defect.Search
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Rat.Encodable

/-! A finite executable certificate for a simple eigenpair of an operator
known through a rational matrix enclosure, and completeness at every actual
simple eigenpair. -/
namespace Maxwell.Defect
open Filter Topology InnerProductSpace Module.End

structure SimpleCertificate (n : ℕ) where
  target : ℚ
  residual : ℚ
  gap : ℚ
  vector : Fin n → ℚ
  congruence : Certificate.LDLWitness n

def SimpleCertificate.accepts {n : ℕ} (c : SimpleCertificate n)
    (T : Matrix (Fin n) (Fin n) ℚ) (error : ℚ) : Bool :=
  decide (T.IsSymm ∧ c.vector ≠ 0 ∧ 0 ≤ error ∧ 0 < c.residual ∧
    2 * (error + 2 * c.residual) < c.gap ∧
    rationalResidualSq T c.vector c.target ≤ c.residual ^ 2 * rationalNormSq c.vector ∧
    c.congruence.accepts (rationalGapMatrix T c.vector c.target c.gap) = true)

/-- Accepted finite rational checks enclose an actual simple eigenpair of
the target operator, including a certified complementary separation. -/
theorem SimpleCertificate.sound {n : ℕ} (c : SimpleCertificate n)
    (T : Matrix (Fin n) (Fin n) ℚ) (error : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hcheck : c.accepts T error = true) :
    ∃ ν : ℝ, ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧ S x = ν • x ∧
      |ν - (c.target : ℝ)| ≤ (error : ℝ) + 2 * (c.residual : ℝ) ∧
      Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      0 < inner ℝ (rationalUnitVector c.vector) x ∧
      ‖x - rationalUnitVector c.vector‖ ≤
        4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ) ∧
      ∀ (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)), ‖y‖ = 1 → S y = ρ • y → ν ≠ ρ →
        (c.gap : ℝ) - 2 * ((error : ℝ) + 2 * (c.residual : ℝ)) ≤ |ρ - ν| := by
  obtain ⟨hT, hv, _, hrespos, hsmall, hres, hldl⟩ := of_decide_eq_true hcheck
  apply rationalResidual_approximation_sound T c.vector c.target c.residual c.gap
    c.congruence S error hT hv hrespos.le hres hldl hS happrox
  exact_mod_cast hsmall

/-- All certificate fields have an explicit finite encoding. -/
def simpleCertificateEquiv (n : ℕ) : SimpleCertificate n ≃
    ℚ × ℚ × ℚ × (Fin n → ℚ) × Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ) where
  toFun c := ⟨c.target, c.residual, c.gap, c.vector, c.congruence.lower, c.congruence.diagonal⟩
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, ⟨c.2.2.2.2.1, c.2.2.2.2.2⟩⟩
  left_inv c := by cases c; rfl
  right_inv c := rfl

instance (n : ℕ) : Encodable (SimpleCertificate n) := by
  letI : Encodable (Matrix (Fin n) (Fin n) ℚ) :=
    inferInstanceAs (Encodable (Fin n → Fin n → ℚ))
  exact Encodable.ofEquiv _ (simpleCertificateEquiv n)

/-- Exact decoding followed by a finite rational check is an executable
search predicate; malformed codes are rejected. -/
def simpleCertificateCheck {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ)
    (error : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := SimpleCertificate n) code with
  | none => false
  | some c => c.accepts T error

@[simp] theorem simpleCertificateCheck_encode {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℚ) (error : ℚ) (c : SimpleCertificate n) :
    simpleCertificateCheck T error (Encodable.encode c) = c.accepts T error := by
  simp [simpleCertificateCheck, Encodable.encodek]

/-- Certificates can achieve arbitrarily tight target, direction, and
error bounds. This strengthens termination to completeness for every finite
collection of strict spectral and overlap margins. -/
theorem simpleCertificate_complete_eventually {n : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0)) (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∀ᶠ k in atTop, ∃ c : SimpleCertificate n, c.accepts (T k) (error k) = true ∧
      |(c.target : ℝ) - μ| < accuracy ∧
      ‖rationalUnitVector c.vector - u‖ < accuracy ∧
      (error k : ℝ) + 2 * (c.residual : ℝ) < accuracy ∧
      0 < c.gap ∧
      4 * ((error k : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ) < accuracy := by
  obtain ⟨γ, hγ, hgap⟩ := simple_eigenpair_has_complementary_gap S u μ hu hSu hsimple
  obtain ⟨g, hg0, hγg⟩ := exists_rat_btwn (by positivity : (0 : ℝ) < γ / 2)
  obtain ⟨ε, hε0, hεbudget⟩ := exists_rat_btwn (by positivity :
    (0 : ℝ) < min ((g : ℝ) / 8) (min (accuracy / 8) ((g : ℝ) * accuracy / 32)))
  have hεg : (ε : ℝ) < (g : ℝ) / 8 := lt_of_lt_of_le hεbudget (min_le_left _ _)
  have hεaccuracy : (ε : ℝ) < accuracy / 8 :=
    lt_of_lt_of_le hεbudget ((min_le_right _ _).trans (min_le_left _ _))
  have hεdirection : (ε : ℝ) < (g : ℝ) * accuracy / 32 :=
    lt_of_lt_of_le hεbudget ((min_le_right _ _).trans (min_le_right _ _))
  have hg : (0 : ℚ) < g := by exact_mod_cast hg0
  have hε : (0 : ℚ) < ε := by exact_mod_cast hε0
  obtain ⟨target, htarget⟩ := exists_rational_target_sequence μ
  obtain ⟨v, hv0, hvlim⟩ := exists_rational_unit_sequence u hu
  have hv : ∀ᶠ k in atTop, ‖rationalUnitVector (v k)‖ = 1 := by
    filter_upwards [hv0] with k hk
    exact rationalUnitVector_norm _ hk
  have hpass := residual_quadratic_certificate_eventually S u μ γ g ε
    (fun k => rationalOperator (T k)) (fun k => rationalUnitVector (v k))
    (fun k => (target k : ℝ)) hu hSu hγ hg0.le hγg.le hε0 hgap
    (fun k => rationalOperator_symmetric (T k) (hT k)) hv hTlim hvlim htarget
  have herr := herrlim.eventually_lt_const (by positivity :
    (0 : ℝ) < min ((g : ℝ) / 8) (min (accuracy / 4) ((g : ℝ) * accuracy / 16)))
  have htar : Tendsto (fun k => |(target k : ℝ) - μ|) atTop (𝓝 0) := by
    simpa using (htarget.sub (tendsto_const_nhds (x := μ))).abs
  have hdir : Tendsto (fun k => ‖rationalUnitVector (v k) - u‖) atTop (𝓝 0) := by
    simpa only [rationalUnitVector, rationalVector, sub_self, norm_zero] using
      (hvlim.sub (tendsto_const_nhds (x := u))).norm
  filter_upwards [hv0, hpass, herr, htar.eventually_lt_const haccuracy,
    hdir.eventually_lt_const haccuracy] with k hk0 hkpass hkbudget hktar hkdir
  have hkerr : (error k : ℝ) < (g : ℝ) / 8 :=
    lt_of_lt_of_le hkbudget (min_le_left _ _)
  have hkaccuracy : (error k : ℝ) < accuracy / 4 :=
    lt_of_lt_of_le hkbudget ((min_le_right _ _).trans (min_le_left _ _))
  have hkdirection : (error k : ℝ) < (g : ℝ) * accuracy / 16 :=
    lt_of_lt_of_le hkbudget ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 2 * (error k + 2 * ε) < g := by
    have hh : 2 * ((error k : ℝ) + 2 * (ε : ℝ)) < (g : ℝ) := by linarith
    exact_mod_cast hh
  obtain ⟨w, hw⟩ := exists_rational_psd_certificate_of_real
    (rationalGapMatrix (T k) (v k) (target k) g)
    ((rationalGapMatrix_certificate_iff _ _ _ _).mpr hkpass.2.2)
  refine ⟨⟨target k, ε, g, v k, w⟩, ?_, hktar, hkdir, ?_, hg, ?_⟩
  · apply decide_eq_true
    exact ⟨hT k, hk0, herror k, hε, hsmall,
      (rationalResidual_bound_iff _ _ _ _ hk0 hε.le).mpr hkpass.2.1.le, hw⟩
  · dsimp only
    linarith
  · dsimp only
    apply (div_lt_iff₀ hg0).mpr
    nlinarith

/-- Every actual simple eigenpair is certifiable from convergent rational
symmetric matrices and vanishing rational operator error bounds. -/
theorem simpleCertificate_complete {n : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0)) :
    ∃ k, ∃ c : SimpleCertificate n, c.accepts (T k) (error k) = true := by
  obtain ⟨k, c, hc, _⟩ := (simpleCertificate_complete_eventually S u μ T error hu hSu
    hsimple hT herror hTlim herrlim 1 (by norm_num)).exists
  exact ⟨k, c, hc⟩

/-- Fair enumeration of matrix precision and all rational certificate
fields terminates at an actual simple eigenpair. -/
theorem simpleCertificate_search_terminates {n : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (error : ℕ → ℚ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hT : ∀ k, (T k).IsSymm) (herror : ∀ k, 0 ≤ error k)
    (hTlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 S))
    (herrlim : Tendsto (fun k => (error k : ℝ)) atTop (𝓝 0)) :
    ∃ stage, simpleCertificateCheck (T (Nat.unpair stage).1)
      (error (Nat.unpair stage).1) (Nat.unpair stage).2 = true := by
  obtain ⟨k, c, hc⟩ := simpleCertificate_complete S u μ T error hu hSu hsimple hT herror hTlim herrlim
  exact ⟨Nat.pair k (Encodable.encode c), by simp [hc]⟩

end Maxwell.Defect
