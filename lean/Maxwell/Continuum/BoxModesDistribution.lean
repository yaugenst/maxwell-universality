import Maxwell.Continuum.BoxModesGraph
import Maxwell.Continuum.PECDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Interior classical derivatives and the literal distributional pairing

Integration by parts against compact PEC tests identifies derivatives of
zero-extended smooth fields in the interior. The proof does not assume
that zero extension preserves second derivatives at the boundary.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory TopologicalSpace
open scoped ContDiff BigOperators

def complexPartial (f : Space → ℂ) (j : Fin 3) (x : Space) : ℂ :=
  fderiv ℝ f x (coordinateDirection j)

def complexCurl (F : Space → Fin 3 → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  complexPartial (fun y => F y (i + 2)) (i + 1) x -
    complexPartial (fun y => F y (i + 1)) (i + 2) x

theorem continuous_complexPartial (f : Space → ℂ) (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    Continuous (complexPartial f j) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem integral_smooth_mul_partial_test (Ω : Opens Space) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (φ : TestFunction Ω ℂ ⊤) (j : Fin 3) :
    (∫ x, f x * partialSchwartz j (testSchwartz Ω φ) x) =
      -(∫ x, complexPartial f j x * φ x) := by
  have hc : HasCompactSupport (fun x => partialSchwartz j (testSchwartz Ω φ) x) :=
    φ.hasCompactSupport.fderiv_apply ℝ (coordinateDirection j)
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := coordinateDirection j)
  · exact ((continuous_complexPartial f hf j).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  · exact (hf.continuous.mul (partialSchwartz j (testSchwartz Ω φ)).continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  · intro x _
    exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt
      (coordinateDirection j)
  · intro x _
    exact ((testSchwartz Ω φ).hasFDerivAt x).hasLineDerivAt (coordinateDirection j)

theorem partial_test_zero_outside (Ω : Opens Space) (φ : TestFunction Ω ℂ ⊤)
    (j : Fin 3) (x : Space) (hx : x ∉ Ω) :
    partialSchwartz j (testSchwartz Ω φ) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  exact hx (φ.tsupport_subset
    ((SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection j) (testSchwartz Ω φ)) hs))

theorem distributionPairing_zeroExtension (Ω : Opens Space) (u : FieldL2)
    (F : Space → Fin 3 → ℂ)
    (hu : ∀ i, (u i : Space → ℂ) =ᵐ[volume] (Ω : Set Space).indicator (fun x => F x i))
    (φ : TestField Ω) :
    distributionPairing (fieldDistribution u) (testSchwartzField Ω φ) =
      ∑ i, ∫ x, F x i * φ i x := by
  unfold distributionPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [fieldDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hu i] with x hx
  change φ i x * u i x = F x i * φ i x
  rw [hx]
  by_cases hΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hΩ]
    exact mul_comm _ _
  · rw [Set.indicator_of_notMem hΩ, (φ i).zero_on_compl hΩ]
    simp only [Pi.zero_apply, mul_zero]

theorem distributionPairing_curl_zeroExtension (Ω : Opens Space) (u : FieldL2)
    (F : Space → Fin 3 → ℂ)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x => F x i))
    (hu : ∀ i, (u i : Space → ℂ) =ᵐ[volume] (Ω : Set Space).indicator (fun x => F x i))
    (φ : TestField Ω) :
    distributionPairing (curlDistribution (fieldDistribution u)) (testSchwartzField Ω φ) =
      ∑ i, ∫ x, complexCurl F x i * φ i x := by
  rw [curlDistribution_pairing]
  have hpart (i j k : Fin 3) :
      (∫ x, partialSchwartz j (testSchwartz Ω (φ k)) x * u i x) =
        -(∫ x, complexPartial (fun y => F y i) j x * φ k x) := by
    calc
      (∫ x, partialSchwartz j (testSchwartz Ω (φ k)) x * u i x) =
          ∫ x, F x i * partialSchwartz j (testSchwartz Ω (φ k)) x := by
        apply integral_congr_ae
        filter_upwards [hu i] with x hx
        rw [hx]
        by_cases hΩ : x ∈ Ω
        · rw [Set.indicator_of_mem hΩ]
          exact mul_comm _ _
        · rw [Set.indicator_of_notMem hΩ, partial_test_zero_outside Ω (φ k) j x hΩ]
          simp only [mul_zero]
      _ = _ := integral_smooth_mul_partial_test Ω _ (hF i) (φ k) j
  have hint (i j k : Fin 3) : Integrable
      (fun x => partialSchwartz j (testSchwartz Ω (φ k)) x * u i x) volume := by
    have hs : MemLp (fun x => partialSchwartz j (testSchwartz Ω (φ k)) x) 2 volume :=
      (partialSchwartz j (testSchwartz Ω (φ k))).memLp 2 volume
    exact hs.integrable_mul (Lp.memLp (u i))
  have hout (i j k : Fin 3) : Integrable
      (fun x => complexPartial (fun y => F y i) j x * φ k x) volume :=
    ((continuous_complexPartial _ (hF i) j).mul (φ k).continuous).integrable_of_hasCompactSupport (φ k).hasCompactSupport.mul_left
  simp only [distributionPairing, fieldDistribution_apply, Lp.toTemperedDistribution_apply,
    curlSchwartz_apply]
  change (∑ i, ∫ x,
    (partialSchwartz (i + 1) (testSchwartz Ω (φ (i + 2))) x -
      partialSchwartz (i + 2) (testSchwartz Ω (φ (i + 1))) x) * u i x) = _
  simp_rw [sub_mul, integral_sub (hint _ _ _) (hint _ _ _), hpart]
  simp only [complexCurl, sub_mul]
  simp_rw [integral_sub (hout _ _ _) (hout _ _ _)]
  simp only [Fin.sum_univ_three]
  norm_num
  ring

#print axioms distributionPairing_curl_zeroExtension

end Maxwell.Continuum.BoxModes
