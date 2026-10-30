import Maxwell.Continuum.ProfileRawApproximation
import Maxwell.Continuum.ProfileEndpointMatch
import Maxwell.Continuum.ProfileEndpointCoefficients
import Maxwell.Continuum.ProfileZeroExtension

/-! The finite dyadic radial encoder, its exact endpoint identities, and C1 error. -/

namespace Maxwell.Continuum.Profile

open Set

def encodedCoefficient (N j : ℕ) : Dyadic (profileWorkBits N) :=
  matchedCoefficient (profileDegree N) (roundedCoefficient N) j

def profileData (N : ℕ) : List (Dyadic (profileWorkBits N)) :=
  List.ofFn (fun j : Fin (profileDegree N) => encodedCoefficient N j)

theorem profileData_length (N : ℕ) : (profileData N).length=profileDegree N := by
  simp only [profileData, List.length_ofFn]

noncomputable def encodedProfile (N : ℕ) : ℝ → ℝ :=
  finiteProfile (profileDegree N) (fun j => ((encodedCoefficient N j).value : ℝ))

theorem encodedProfile_eq (N : ℕ) : encodedProfile N=endpointMatch (rawProfile N) := by
  funext t
  have hD : 2 ≤ profileDegree N := by
    unfold profileDegree
    exact (by decide : 2 ≤ 2^2).trans (Nat.pow_le_pow_left (by omega : 2 ≤ 128*(N+256)) 2)
  rw [encodedProfile]
  change finiteProfile (profileDegree N)
    (fun j => ((matchedCoefficient (profileDegree N) (roundedCoefficient N) j).value : ℝ)) t=_
  rw [matchedCoefficient_evaluation _ hD]
  change rawProfile N t-rawProfile N 1-rawProfileDerivative N 1*(t-1)=_
  rw [endpointMatch, (rawProfile_hasDerivAt N 1).deriv]

theorem encodedProfile_contDiff (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (encodedProfile N) :=
  finiteProfile_contDiff _ _

theorem encodedProfile_endpoint (N : ℕ) : encodedProfile N 1=0 ∧ deriv (encodedProfile N) 1=0 := by
  rw [encodedProfile_eq]
  exact ⟨endpointMatch_value _, endpointMatch_derivative
    ((rawProfile_contDiff N).differentiable (by simp))⟩

theorem encodedProfile_error (N : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |radial t-encodedProfile N t| ≤ (1/2 : ℝ)^(N+24) ∧
    |deriv radial t-deriv (encodedProfile N) t| ≤ (1/2 : ℝ)^(N+24) := by
  have hv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := (rawProfile_errors N hs).1
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |deriv radial s-deriv (rawProfile N) s| ≤ (1/2 : ℝ)^(N+26) := by
    rw [(rawProfile_hasDerivAt N s).deriv]
    exact (rawProfile_errors N hs).2
  have hval := endpointMatch_error (by positivity : 0 ≤ (1/2 : ℝ)^(N+26)) hv hd ht
  have hder := endpointMatch_derivative_error
    ((rawProfile_contDiff N).differentiable (by simp)) hd ht
  rw [← encodedProfile_eq] at hval hder
  have hscale : 3*(1/2 : ℝ)^(N+26) ≤ (1/2 : ℝ)^(N+24) := by
    rw [show N+26=(N+24)+2 by omega, pow_add]
    nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (N+24)]
  exact ⟨hval.trans hscale, hder.trans (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (N+26)])⟩

noncomputable def encodedRoot (N : ℕ) (y : Space) : ℝ := zeroExtension (encodedProfile N) (‖y‖^2)

theorem encodedRoot_contDiff (N : ℕ) : ContDiff ℝ 1 (encodedRoot N) :=
  (zeroExtension_contDiff_one ((encodedProfile_contDiff N).of_le (by simp))
    (encodedProfile_endpoint N).1 (encodedProfile_endpoint N).2).comp
    (contDiff_norm_sq (E := Space) ℝ)

theorem encodedRoot_error (N : ℕ) (y : Space) :
    |Well.qw y-encodedRoot N y| ≤ (1/2 : ℝ)^(N+24) := by
  by_cases hy : ‖y‖^2<1
  · rw [encodedRoot, zeroExtension, ite_eq_left hy, Well.qw_eq_glue]
    exact (encodedProfile_error N ⟨sq_nonneg _,hy.le⟩).1
  · have hy1 : 1 ≤ ‖y‖ := by nlinarith [norm_nonneg y]
    rw [encodedRoot, zeroExtension, ite_eq_right hy, (Well.qw_zero_iff y).mpr hy1,
      sub_self, abs_zero]
    positivity

theorem encodedRoot_zero {N : ℕ} {y : Space} (hy : 1 ≤ ‖y‖) : encodedRoot N y=0 := by
  have hs : ¬ ‖y‖^2<1 := by nlinarith
  exact ite_eq_right hs

theorem encodedRoot_bound (N : ℕ) (y : Space) : |encodedRoot N y| ≤ 2 := by
  have he := encodedRoot_error N y
  have hp : (1/2 : ℝ)^(N+24) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le (encodedRoot N y) (Well.qw y) 0
  simp only [sub_zero, abs_sub_comm _ (Well.qw y), abs_of_nonneg (Well.qw_nonneg y)] at ht
  linarith [Well.qw_le_one y]

theorem encodedRoot_square_error (N : ℕ) (y : Space) :
    |Well.w y-(encodedRoot N y)^2| ≤ 3*(1/2 : ℝ)^(N+24) := by
  rw [← Well.qw_sq]
  calc
    _ = |Well.qw y-encodedRoot N y| * |Well.qw y+encodedRoot N y| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (1/2 : ℝ)^(N+24)*3 := mul_le_mul (encodedRoot_error N y)
      ((abs_add_le _ _).trans (by
        rw [abs_of_nonneg (Well.qw_nonneg y)]
        linarith [Well.qw_le_one y, encodedRoot_bound N y])) (abs_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms encodedProfile_error
#print axioms encodedRoot_contDiff
#print axioms encodedRoot_square_error

end Maxwell.Continuum.Profile
