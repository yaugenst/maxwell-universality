import Maxwell.Spectral.YeeAnalytic
import Maxwell.Spectral.SeparatedInverse
import Maxwell.Green.TorusContour
import Mathlib.Analysis.Analytic.Constructions

/-! Uniform complex resolvent bounds from a real compact spectral gap.

Invertibility on the displaced contour is a conclusion. Compactness upgrades
the open inverse map at the actual real fibers to a common perturbation
radius and a common inverse norm bound.
-/

noncomputable section

namespace Maxwell.Spectral.ComplexContourGap

open Filter Set
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem analyticAt_inverse_operator {T : H →L[ℂ] H} (hT : T.IsInvertible) :
    AnalyticAt ℂ (ContinuousLinearMap.inverse (R := ℂ) (M := H)) T := by
  obtain ⟨B, rfl⟩ := hT
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  exact analyticAt_inverse B.toUnit

theorem analyticAt_inverse_family {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {A : Z → H →L[ℂ] H} {z : Z} (hA : AnalyticAt ℂ A z)
    (hi : (A z).IsInvertible) :
    AnalyticAt ℂ (fun w => (A w).inverse) z :=
  (analyticAt_inverse_operator hi).comp hA

/-- A continuous perturbation of invertible real fibers stays uniformly
invertible over a compact set; the inverse norm has one common bound. -/
theorem compact_inverse_neighborhood
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    (K : Set X) (hK : IsCompact K) (F : V × X → H →L[ℂ] H)
    (hF : ∀ q ∈ K, ContinuousAt F (0, q))
    (hreal : ∀ q ∈ K, (F (0, q)).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ v, ‖v‖ < r → ∀ q ∈ K,
        (F (v, q)).IsInvertible ∧ ‖(F (v, q)).inverse‖ ≤ C := by
  have hinv (q : X) (hq : q ∈ K) :
      ContinuousAt (fun z : V × X => (F z).inverse) (0, q) :=
    (analyticAt_inverse_operator (hreal q hq)).continuousAt.comp (hF q hq)
  have hslice : ContinuousOn (fun q => (F (0, q)).inverse) K := by
    intro q hq
    exact ((hinv q hq).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := (hK.image_of_continuousOn hslice).isBounded.exists_norm_le
  let C := max C₀ 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have he : ∀ᶠ v in 𝓝 (0 : V), ∀ q ∈ K,
      (F (v, q)).IsInvertible ∧ ‖(F (v, q)).inverse‖ ≤ C := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    have hi := (hF q hq).tendsto.eventually (hreal q hq).eventually_nhds
    have hb : ‖(F (0, q)).inverse‖ < C :=
      lt_of_le_of_lt (hC₀ _ (mem_image_of_mem _ hq))
        (lt_add_of_le_of_pos (le_max_left C₀ 0) zero_lt_one)
    have hn := (hinv q hq).norm.eventually (gt_mem_nhds hb)
    filter_upwards [hi, hn] with z hz hnz
    exact ⟨hz, hnz.le⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨r, C, hr, hC, ?_⟩
  intro v hv
  exact hball v (by simpa using hv)

open YeeAnalytic PeriodicYee PrimitiveYee

theorem holomorphicOperator_energy_add (material : Cell20 → ℝ) (k : Momentum)
    (energy δ : ℝ) (z : ComplexMomentum) :
    holomorphicOperator material k (energy + δ) z =
      holomorphicOperator material k energy z - (δ : ℂ) • 1 := by
  change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (holomorphicFiber material k z - ((energy + δ : ℝ) : ℂ) • 1) =
    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (holomorphicFiber material k z - (energy : ℂ) • 1) - (δ : ℂ) • 1
  simp only [map_sub, map_smul, map_one, map_add, Complex.ofReal_add, add_smul]
  abel

def realOperator (material : Cell20 → ℝ) (k q : Momentum) :
    EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  holomorphicOperator material k 0 (realMomentum q)

theorem realOperator_symmetric (material : Cell20 → ℝ) (k q : Momentum) :
    (realOperator material k q).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
    holomorphicFiber_real_hermitian material k q

theorem realOperator_shift (material : Cell20 → ℝ) (k q : Momentum) (energy : ℝ) :
    SeparatedInverse.shifted (realOperator material k q) energy =
      YeeTaylor.shiftedCenteredOperator material k q energy := by
  have h := holomorphicOperator_energy_add material k 0 energy (realMomentum q)
  simpa only [zero_add, holomorphicOperator_real, SeparatedInverse.shifted,
    realOperator, ContinuousLinearMap.one_def] using h.symm

@[simp] theorem norm_realMomentum (q : Momentum) : ‖realMomentum q‖ = ‖q‖ := by
  simp only [Pi.norm_def, realMomentum, Complex.nnnorm_real]

/-- The real-fiber gap controls an entire complex neighborhood of every
point in the compact far set for the actual centered Yee family. -/
theorem yee_compact_inverse_neighborhood
    (material : Cell20 → ℝ) (k : Momentum) (energy : ℝ)
    (K : Set Momentum) (hK : IsCompact K)
    (hreal : ∀ q ∈ K,
      (YeeTaylor.shiftedCenteredOperator material k q energy).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ v : ComplexMomentum, ‖v‖ < r → ∀ q ∈ K,
        (holomorphicOperator material k energy (realMomentum q + v)).IsInvertible ∧
        ‖(holomorphicOperator material k energy (realMomentum q + v)).inverse‖ ≤ C := by
  apply compact_inverse_neighborhood K hK
    (fun z : ComplexMomentum × Momentum =>
      holomorphicOperator material k energy (realMomentum z.2 + z.1))
  · intro q _hq
    apply (holomorphicOperator_analyticAt material k energy _).continuousAt.comp
    unfold realMomentum
    fun_prop
  · intro q hq
    simpa only [add_zero, holomorphicOperator_real] using hreal q hq

/-- Both complex momentum and energy are perturbed together. The resulting
radius and inverse bound are independent of the small spectral parameter. -/
theorem yee_compact_inverse_neighborhood_energy
    (material : Cell20 → ℝ) (k : Momentum) (energy : ℝ)
    (K : Set Momentum) (hK : IsCompact K)
    (hreal : ∀ q ∈ K,
      (YeeTaylor.shiftedCenteredOperator material k q energy).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ δ : ℝ, |δ| < r → ∀ v : ComplexMomentum, ‖v‖ < r → ∀ q ∈ K,
        (holomorphicOperator material k (energy + δ) (realMomentum q + v)).IsInvertible ∧
        ‖(holomorphicOperator material k (energy + δ) (realMomentum q + v)).inverse‖ ≤ C := by
  let F := fun z : (ComplexMomentum × ℝ) × Momentum =>
    holomorphicOperator material k energy (realMomentum z.2 + z.1.1) - (z.1.2 : ℂ) • 1
  have hF : ∀ q ∈ K, ContinuousAt F (0, q) := by
    intro q _hq
    apply ContinuousAt.sub
    · apply (holomorphicOperator_analyticAt material k energy _).continuousAt.comp
      unfold realMomentum
      fun_prop
    · fun_prop
  have hF0 : ∀ q ∈ K, (F (0, q)).IsInvertible := by
    intro q hq
    change (holomorphicOperator material k energy (realMomentum q + 0) - (0 : ℂ) • 1).IsInvertible
    rw [add_zero]
    rw [zero_smul ℂ (1 : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric)]
    rw [sub_zero, holomorphicOperator_real]
    exact hreal q hq
  obtain ⟨r, C, hr, hC, h⟩ := compact_inverse_neighborhood K hK F hF hF0
  refine ⟨r, C, hr, hC, ?_⟩
  intro δ hδ v hv q hq
  have hz : ‖(v, δ)‖ < r := by simpa only [Prod.norm_def, max_lt_iff, Real.norm_eq_abs] using And.intro hv hδ
  simpa only [F, holomorphicOperator_energy_add] using h (v, δ) hz q hq

/-- The same radius covers every intermediate contour and every direction
with sufficiently small norm. The inverse is analytic at every point of
these contours, and its norm bound is uniform in momentum and deformation. -/
theorem yee_compact_contour_inverse
    (material : Cell20 → ℝ) (k : Momentum) (energy : ℝ)
    (K : Set Momentum) (hK : IsCompact K)
    (hreal : ∀ q ∈ K,
      (YeeTaylor.shiftedCenteredOperator material k q energy).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ β : Momentum, ‖β‖ < r → ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ K,
        (holomorphicOperator material k energy (Maxwell.Green.contourShift β s q)).IsInvertible ∧
        ‖(holomorphicOperator material k energy
          (Maxwell.Green.contourShift β s q)).inverse‖ ≤ C ∧
        AnalyticAt ℂ (fun z => (holomorphicOperator material k energy z).inverse)
          (Maxwell.Green.contourShift β s q) := by
  obtain ⟨r, C, hr, hC, h⟩ := yee_compact_inverse_neighborhood material k energy K hK hreal
  refine ⟨r, C, hr, hC, ?_⟩
  intro β hβ s hs q hq
  let v : ComplexMomentum := s • (Complex.I • realMomentum β)
  have hv : ‖v‖ < r := by
    calc
      ‖v‖ = s * ‖β‖ := by
        simp [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      _ ≤ ‖β‖ := mul_le_of_le_one_left (norm_nonneg β) hs.2
      _ < r := hβ
  have hz : realMomentum q + v = Maxwell.Green.contourShift β s q := rfl
  obtain ⟨hi, hn⟩ := h v hv q hq
  rw [hz] at hi hn
  exact ⟨hi, hn, analyticAt_inverse_family
    (holomorphicOperator_analyticAt material k energy _) hi⟩

/-- The actual real eigenvalue gap constructs the physical shifted inverse
and proves its quantitative norm bound. -/
theorem yee_real_inverse_of_spectral_gap
    (material : Cell20 → ℝ) (k q : Momentum) (energy g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, g ≤ |(realOperator_symmetric material k q).eigenvalues rfl i - energy|) :
    (YeeTaylor.shiftedCenteredOperator material k q energy).IsInvertible ∧
    ‖(YeeTaylor.shiftedCenteredOperator material k q energy).inverse‖ ≤ g⁻¹ := by
  let B := SeparatedInverse.equiv (realOperator material k q)
    (realOperator_symmetric material k q) energy g hg hgap
  have hB : (B : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric) =
      YeeTaylor.shiftedCenteredOperator material k q energy :=
    realOperator_shift material k q energy
  refine ⟨⟨B, hB⟩, ?_⟩
  rw [← hB, ContinuousLinearMap.inverse_equiv]
  exact SeparatedInverse.inverse_norm_le (realOperator material k q)
    (realOperator_symmetric material k q) energy g hg hgap

/-- Uniform complex contour invertibility for the concrete Yee family follows
from a real spectral separation on the compact far region. The contour,
energy variation, inverse bound and inverse analyticity share one radius. -/
theorem yee_compact_contour_inverse_of_spectral_gap
    (material : Cell20 → ℝ) (k : Momentum) (energy g : ℝ) (hg : 0 < g)
    (K : Set Momentum) (hK : IsCompact K)
    (hgap : ∀ q ∈ K, ∀ i,
      g ≤ |(realOperator_symmetric material k q).eigenvalues rfl i - energy|) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ δ : ℝ, |δ| < r → ∀ β : Momentum, ‖β‖ < r →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ K,
        (holomorphicOperator material k (energy + δ)
          (Maxwell.Green.contourShift β s q)).IsInvertible ∧
        ‖(holomorphicOperator material k (energy + δ)
          (Maxwell.Green.contourShift β s q)).inverse‖ ≤ C ∧
        AnalyticAt ℂ (fun z => (holomorphicOperator material k (energy + δ) z).inverse)
          (Maxwell.Green.contourShift β s q) := by
  have hreal : ∀ q ∈ K,
      (YeeTaylor.shiftedCenteredOperator material k q energy).IsInvertible :=
    fun q hq => (yee_real_inverse_of_spectral_gap material k q energy g hg (hgap q hq)).1
  obtain ⟨r, C, hr, hC, h⟩ :=
    yee_compact_inverse_neighborhood_energy material k energy K hK hreal
  refine ⟨r, C, hr, hC, ?_⟩
  intro δ hδ β hβ s hs q hq
  let v : ComplexMomentum := s • (Complex.I • realMomentum β)
  have hv : ‖v‖ < r := by
    calc
      ‖v‖ = s * ‖β‖ := by
        simp [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      _ ≤ ‖β‖ := mul_le_of_le_one_left (norm_nonneg β) hs.2
      _ < r := hβ
  have hz : realMomentum q + v = Maxwell.Green.contourShift β s q := rfl
  obtain ⟨hi, hn⟩ := h δ hδ v hv q hq
  rw [hz] at hi hn
  exact ⟨hi, hn, analyticAt_inverse_family
    (holomorphicOperator_analyticAt material k (energy + δ) _) hi⟩

/-- Removing any open collection of local edge neighborhoods from the closed
torus cell leaves the compact far region needed above. -/
theorem isCompact_far_torus (a p : ℝ) (U : Set Momentum) (hU : IsOpen U) :
    IsCompact (Maxwell.Green.torusCube a p \ U) :=
  (Maxwell.Green.isCompact_torusCube a p).diff hU

/-- Tube notation for a compact part of the real torus, including its far
region. Its spectral and spatial normalizations are those of `contourShift`. -/
def tubeOver (K : Set Momentum) (β : Momentum) : Set ComplexMomentum :=
  (fun z : ℝ × Momentum => Maxwell.Green.contourShift β z.1 z.2) ''
    (Icc (0 : ℝ) 1 ×ˢ K)

theorem isCompact_tubeOver (K : Set Momentum) (hK : IsCompact K) (β : Momentum) :
    IsCompact (tubeOver K β) :=
  (isCompact_Icc.prod hK).image (Maxwell.Green.continuous_contourShift β)

/-- The pointwise contour conclusion has the `AnalyticOnNhd` form required
by periodic contour deformation, with the same inverse norm constant. -/
theorem yee_compact_contour_tube_of_spectral_gap
    (material : Cell20 → ℝ) (k : Momentum) (energy g : ℝ) (hg : 0 < g)
    (K : Set Momentum) (hK : IsCompact K)
    (hgap : ∀ q ∈ K, ∀ i,
      g ≤ |(realOperator_symmetric material k q).eigenvalues rfl i - energy|) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ δ : ℝ, |δ| < r → ∀ β : Momentum, ‖β‖ < r →
        AnalyticOnNhd ℂ (fun z => (holomorphicOperator material k (energy + δ) z).inverse)
          (tubeOver K β) ∧
        ∀ z ∈ tubeOver K β,
          (holomorphicOperator material k (energy + δ) z).IsInvertible ∧
          ‖(holomorphicOperator material k (energy + δ) z).inverse‖ ≤ C := by
  obtain ⟨r, C, hr, hC, h⟩ :=
    yee_compact_contour_inverse_of_spectral_gap material k energy g hg K hK hgap
  refine ⟨r, C, hr, hC, ?_⟩
  intro δ hδ β hβ
  constructor
  · rintro _ ⟨⟨s, q⟩, ⟨hs, hq⟩, rfl⟩
    exact (h δ hδ β hβ s hs q hq).2.2
  · rintro _ ⟨⟨s, q⟩, ⟨hs, hq⟩, rfl⟩
    exact ⟨(h δ hδ β hβ s hs q hq).1, (h δ hδ β hβ s hs q hq).2.1⟩

end Maxwell.Spectral.ComplexContourGap
