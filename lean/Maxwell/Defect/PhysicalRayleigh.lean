import Maxwell.Defect.ResolventRayleigh
import Maxwell.Defect.ProfileParseval

/-! A lower Rayleigh bound for the genuine infinite periodic inverse.
The selected local Bloch pole is integrated over its chart, while Parseval
controls all negative bands by the norm of the same physical source. -/
namespace Maxwell.Defect

open MeasureTheory Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.BlochResolvent Maxwell.Green.PhysicalCompression
open scoped ENNReal

noncomputable section

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrixResolvent_inner (H : Matrix n n ℂ) (z : ℝ) (v : EuclideanSpace ℂ n) :
    inner ℂ v (finiteResolvent (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H) z v) =
      ∑ i, star (v i) * (Ring.inverse (H - (z : ℂ) • 1)).mulVec v i := by
  have hh := ringEquiv_map_ringInverse
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toRingEquiv (H - (z : ℂ) • 1)
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse (H - (z : ℂ) • 1)) =
    Ring.inverse (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - (z : ℂ) • 1)) at hh
  simp only [map_sub, map_smul, map_one] at hh
  unfold finiteResolvent
  rw [← hh, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, (Ring.inverse (H - (z : ℂ) • 1)).mulVec v i * star (v i)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem matrixResolvent_lower (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (z g : ℝ) (hg : 0 < g) (hz : z ∉ spectrum ℝ H)
    (hgap : ∀ t ∈ spectrum ℝ H, t ≤ z - g ∨ z ≤ t) (v : EuclideanSpace ℂ n) :
    -(‖v‖ ^ 2 / g) ≤
      (∑ i, star (v i) * (Ring.inverse (H - (z : ℂ) • 1)).mulVec v i).re := by
  let A := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H
  have hHerm : IsSelfAdjoint H := hH
  have hA : IsSelfAdjoint A := hHerm.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
  have hs : spectrum ℂ A = spectrum ℂ H := AlgEquiv.spectrum_eq
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H
  have hz' : (z : ℂ) ∉ spectrum ℂ A := by
    rw [hs]
    exact fun h => hz ((spectrum.algebraMap_mem_iff ℂ).mp h)
  have hg' : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ A → t ≤ z - g ∨ z ≤ t := by
    intro t ht
    rw [hs] at ht
    exact hgap t ((spectrum.algebraMap_mem_iff ℂ).mp ht)
  simpa only [A, matrixResolvent_inner] using
    finiteResolvent_lower A hA.isSymmetric z g hg hz' hg' v

theorem matrixResolvent_selected_lower (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (z g lam : ℝ) (hg : 0 < g) (hz : z ∉ spectrum ℝ H)
    (hgap : ∀ t ∈ spectrum ℝ H, t ≤ z - g ∨ z ≤ t)
    (hlam : z < lam) (φ : EuclideanSpace ℂ n) (hunit : ‖φ‖ = 1)
    (heig : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H φ = (lam : ℂ) • φ)
    (v : EuclideanSpace ℂ n) :
    ‖inner ℂ φ v‖ ^ 2 / (lam - z) - ‖v‖ ^ 2 / g ≤
      (∑ i, star (v i) * (Ring.inverse (H - (z : ℂ) • 1)).mulVec v i).re := by
  let A := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H
  have hHerm : IsSelfAdjoint H := hH
  have hA : IsSelfAdjoint A := hHerm.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
  have hs : spectrum ℂ A = spectrum ℂ H := AlgEquiv.spectrum_eq
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H
  have hz' : (z : ℂ) ∉ spectrum ℂ A := by
    rw [hs]
    exact fun h => hz ((spectrum.algebraMap_mem_iff ℂ).mp h)
  have hg' : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ A → t ≤ z - g ∨ z ≤ t := by
    intro t ht
    rw [hs] at ht
    exact hgap t ((spectrum.algebraMap_mem_iff ℂ).mp ht)
  simpa only [A, matrixResolvent_inner] using
    finiteResolvent_selected_lower A hA.isSymmetric z g lam hg hz' hg' hlam φ hunit heig v

end Matrix

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {ι : Type*} [Fintype ι]

theorem profile_component_continuous (edges : ι → Edge) (a : ι → ℂ) (r : Edge20) :
    Continuous (fun t : Torus => profile edges a t r) := by
  unfold profile
  apply continuous_finsetSum
  intro i _
  split_ifs
  · exact continuous_const.mul (UnitAddTorus.mFourier _).continuous
  · exact continuous_const

theorem scalarAmplitude_continuous (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) :
    Continuous (scalarAmplitude edges a m z) := by
  have hinv : Continuous (fun t : Torus => Ring.inverse (torusElectric m t - (z : ℂ) • 1)) := by
    have hh : (fun t : Torus => Ring.inverse (torusElectric m t - (z : ℂ) • 1)) =
        inverseElectricSymbol m z := by
      funext t
      exact (inverseElectricSymbol_apply m z hz t).symm
    rw [hh]
    exact (inverseElectricSymbol m z).continuous
  unfold scalarAmplitude Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro i _
  apply (profile_component_continuous edges a i).star.mul
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp hinv)).mul
    (profile_component_continuous edges a j)

theorem scalarAmplitude_integrable (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) :
    Integrable (scalarAmplitude edges a m z) :=
  (scalarAmplitude_continuous edges a m z hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The selected local pole in the actual finite Bloch profile. -/
def selectedProfilePole (edges : ι → Edge) (a : ι → ℂ)
    (φ : Torus → EuclideanSpace ℂ Edge20) (lam : Torus → ℝ) (z : ℝ) (t : Torus) : ℝ :=
  ‖inner ℂ (φ t) (WithLp.toLp 2 (profile edges a t))‖ ^ 2 / (lam t - z)

/-- Integrating a local selected-band contribution leaves precisely the
global source norm as the bound for all negative spectral contributions. -/
theorem scalarAmplitude_selected_integral_lower (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (z g : ℝ) (hg : 0 < g)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ t : Torus, ∀ s ∈ spectrum ℝ (torusElectric m t), s ≤ z - g ∨ z ≤ s)
    (U : Set Torus) (hU : MeasurableSet U)
    (φ : Torus → EuclideanSpace ℂ Edge20) (lam : Torus → ℝ)
    (hupper : ∀ t ∈ U, z < lam t) (hunit : ∀ t ∈ U, ‖φ t‖ = 1)
    (heig : ∀ t ∈ U,
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (torusElectric m t) (φ t) =
        (lam t : ℂ) • φ t)
    (hpole : IntegrableOn (selectedProfilePole edges a φ lam z) U) :
    (∫ t in U, selectedProfilePole edges a φ lam z t) - ‖finiteField edges a‖ ^ 2 / g ≤
      (∫ t : Torus, scalarAmplitude edges a m z t).re := by
  let f := selectedProfilePole edges a φ lam z
  let b := fun t : Torus => ‖WithLp.toLp 2 (profile edges a t)‖ ^ 2 / g
  have hi : Integrable (U.indicator f) := hpole.integrable_indicator hU
  have hb : Integrable b := (profile_vector_integrable_norm_sq edges a).div_const g
  have hA := scalarAmplitude_integrable edges a m z hz
  have hre : Integrable (fun t : Torus => (scalarAmplitude edges a m z t).re) := hA.re
  have hpoint (t : Torus) : U.indicator f t - b t ≤ (scalarAmplitude edges a m z t).re := by
    by_cases ht : t ∈ U
    · rw [Set.indicator_of_mem ht]
      exact matrixResolvent_selected_lower (torusElectric m t) (torusElectric_hermitian m t)
        z g (lam t) hg (hz t) (hgap t) (hupper t ht) (φ t) (hunit t ht) (heig t ht)
        (WithLp.toLp 2 (profile edges a t))
    · rw [Set.indicator_of_notMem ht, zero_sub]
      exact matrixResolvent_lower (torusElectric m t) (torusElectric_hermitian m t)
        z g hg (hz t) (hgap t) (WithLp.toLp 2 (profile edges a t))
  calc
    _ = ∫ t : Torus, U.indicator f t - b t := by
      rw [integral_sub hi hb, integral_indicator hU]
      change (∫ t in U, f t) - ‖finiteField edges a‖ ^ 2 / g =
        (∫ t in U, f t) - ∫ t : Torus, ‖WithLp.toLp 2 (profile edges a t)‖ ^ 2 / g
      rw [integral_div, profile_vector_parseval]
    _ ≤ ∫ t : Torus, (scalarAmplitude edges a m z t).re := integral_mono (hi.sub hb) hre hpoint
    _ = _ := integral_re hA

/-- Rayleigh lower bound for the genuine infinite periodic inverse, with
the selected term computed from the same finitely supported physical source. -/
theorem physical_inverse_selected_lower (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z g : ℝ) (hg : 0 < g)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (hgap : ∀ t : Torus, ∀ s ∈ spectrum ℝ (torusElectric m t), s ≤ z - g ∨ z ≤ s)
    (U : Set Torus) (hU : MeasurableSet U)
    (φ : Torus → EuclideanSpace ℂ Edge20) (lam : Torus → ℝ)
    (hupper : ∀ t ∈ U, z < lam t) (hunit : ∀ t ∈ U, ‖φ t‖ = 1)
    (heig : ∀ t ∈ U,
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (torusElectric m t) (φ t) =
        (lam t : ℂ) • φ t)
    (hpole : IntegrableOn (selectedProfilePole edges a φ lam z) U) :
    (∫ t in U, selectedProfilePole edges a φ lam z t) - ‖finiteField edges a‖ ^ 2 / g ≤
      (inner ℂ (finiteField edges a)
        (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)
          (finiteField edges a))).re := by
  have hidentity := scalarCoupling_integral edges a m K hK hm z hz 0
  have heq : translateEdge 0 ∘ edges = edges := by
    funext i
    simp only [Function.comp_apply, translateEdge, smul_zero, sub_zero, Prod.mk.eta]
  simp only [scalarCoupling, heq, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul] at hidentity
  rw [hidentity]
  exact scalarAmplitude_selected_integral_lower edges a m z g hg hz hgap U hU φ lam
    hupper hunit heig hpole

end
end Maxwell.Defect
