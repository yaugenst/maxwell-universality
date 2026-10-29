import Maxwell.Spectral.BoxMixedForm
import Maxwell.Spectral.BoxSchur

/-! Actual finite coordinates for the low-gradient and unrestricted
high-frequency spaces in the auxiliary Schur decomposition. -/

noncomputable section

namespace Maxwell.Spectral.BoxCoordinates

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum Cell20)
open BoxGradient BoxHighCoercivity

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateExtension (support : Finset ι) :
    EuclideanSpace ℂ {i // i ∈ support} →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun i => if h : i ∈ support then x ⟨i,h⟩ else 0)
  map_add' x y := by
    ext i
    change (if h : i ∈ support then x ⟨i,h⟩+y ⟨i,h⟩ else 0) = _
    split_ifs <;> simp_all
  map_smul' a x := by
    ext i
    change (if h : i ∈ support then a*x ⟨i,h⟩ else 0) = _
    split_ifs <;> simp_all
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖(if h : i ∈ support then x ⟨i,h⟩ else 0)‖^2) = _
    calc
      _ = ∑ i ∈ support, ‖(if h : i ∈ support then x ⟨i,h⟩ else 0)‖^2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        rw [dite_eq_right hi]
        norm_num
      _ = ∑ i : {i // i ∈ support},
          ‖(if h : (i : ι) ∈ support then x ⟨i,h⟩ else 0)‖^2 :=
        Finset.sum_subtype support (fun _ => Iff.rfl) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [dite_eq_left i.property]

theorem coordinateExtension_apply (support : Finset ι)
    (x : EuclideanSpace ℂ {i // i ∈ support}) (i : ι) :
    coordinateExtension support x i = if h : i ∈ support then x ⟨i,h⟩ else 0 := rfl

def supportedCoordinates (support : Finset ι) : Submodule ℂ (EuclideanSpace ℂ ι) where
  carrier := {x | ∀ i, i ∉ support → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

def supportedCoordinatesEquiv (support : Finset ι) :
    EuclideanSpace ℂ {i // i ∈ support} ≃ₗᵢ[ℂ] supportedCoordinates support where
  toFun x := ⟨coordinateExtension support x, by
    intro i hi
    simp [coordinateExtension_apply, hi]⟩
  invFun x := WithLp.toLp 2 fun i => (x : EuclideanSpace ℂ ι) i
  left_inv x := by
    ext i
    exact dite_eq_left i.property
  right_inv x := by
    apply Subtype.ext
    ext i
    change (if h : i ∈ support then (x : EuclideanSpace ℂ ι) i else 0) = _
    split_ifs with hi
    · rfl
    · exact (x.property i hi).symm
  map_add' x y := Subtype.ext ((coordinateExtension support).map_add x y)
  map_smul' a x := Subtype.ext ((coordinateExtension support).map_smul a x)
  norm_map' x := (coordinateExtension support).norm_map x

theorem supportedCoordinates_finrank (support : Finset ι) :
    Module.finrank ℂ (supportedCoordinates support) = support.card := by
  rw [← (supportedCoordinatesEquiv support).toLinearEquiv.finrank_eq]
  simp only [finrank_euclideanSpace, Fintype.card_coe]

end Coordinates

abbrev LowGradientCoordinates (low : Finset Frequency) :=
  EuclideanSpace ℂ {f // f ∈ low}

def lowCoefficientEmbedding (low : Finset Frequency) : LowGradientCoordinates low →ₗᵢ[ℂ] Coefficients :=
  coordinateExtension low

theorem lowCoefficientEmbedding_norm (low : Finset Frequency) (g : LowGradientCoordinates low) :
    ‖lowCoefficientEmbedding low g‖ = ‖g‖ := (lowCoefficientEmbedding low).norm_map g

theorem lowCoefficientEmbedding_support (low : Finset Frequency) (g : LowGradientCoordinates low)
    (f : Frequency) (hf : f ∉ low) : lowCoefficientEmbedding low g f = 0 := by
  exact dite_eq_right hf

theorem lowGradientCoordinates_finrank (low : Finset Frequency) :
    Module.finrank ℂ (LowGradientCoordinates low) = low.card := by
  simp only [LowGradientCoordinates, finrank_euclideanSpace, Fintype.card_coe]

def lowGradientEmbedding (c : Momentum) (low : Finset Frequency) :
    LowGradientCoordinates low →L[ℂ] FourierSpace :=
  (BoxMixedForm.gradientOperator c low).comp (lowCoefficientEmbedding low).toContinuousLinearMap

theorem lowGradientEmbedding_apply (c : Momentum) (low : Finset Frequency)
    (g : LowGradientCoordinates low) :
    lowGradientEmbedding c low g = gradient c low (lowCoefficientEmbedding low g) := rfl

theorem lowGradientEmbedding_norm_sq (c : Momentum) (low : Finset Frequency)
    (hv : ∀ f ∈ low, longitudinalVector c f ≠ 0) (g : LowGradientCoordinates low) :
    ‖lowGradientEmbedding c low g‖^2 = 64*‖g‖^2 := by
  rw [lowGradientEmbedding_apply, gradient_norm_sq c low _ hv
    (lowCoefficientEmbedding_support low g), lowCoefficientEmbedding_norm]

theorem lowGradientEmbedding_injective (c : Momentum) (low : Finset Frequency)
    (hv : ∀ f ∈ low, longitudinalVector c f ≠ 0) :
    Function.Injective (lowGradientEmbedding c low) := by
  apply (lowGradientEmbedding c low).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro g hg
  change lowGradientEmbedding c low g = 0 at hg
  have hn := lowGradientEmbedding_norm_sq c low hv g
  rw [hg, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg g])

theorem lowGradientEmbedding_mem_orthogonal (c : Momentum) (low : Finset Frequency)
    (g : LowGradientCoordinates low) :
    lowGradientEmbedding c low g ∈ (transverseSubspace c)ᗮ :=
  BoxMixedForm.gradient_mem_orthogonal c low _

theorem lowGradientEmbedding_auxiliary_lower
    (material : Cell20 → ℝ) (hm : ∀ e, 0 < edgeAverage material e)
    (c q : Momentum) (low : Finset Frequency) (s r σ t' : ℝ)
    (hs : 0 ≤ s) (hq : BoxMagnetic.displacementSize q ≤ s) (hr : 0 < r)
    (hrf : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖) (ht' : t' ≤ 1/64+σ)
    (g : LowGradientCoordinates low) :
    (1-(2*s^2/r^2+64*σ))*‖g‖^2 ≤
      (inner ℂ (lowGradientEmbedding c low g)
        ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
          (lowGradientEmbedding c low g))).re := by
  have h := auxiliary_gradient_lower material hm c q low (lowCoefficientEmbedding low g)
    s r σ t' hs hq hr hrf (lowCoefficientEmbedding_support low g) ht'
  rw [lowCoefficientEmbedding_norm] at h
  exact h

def fieldSupport (support : Finset Frequency) : Finset Electric := Finset.univ.product support

def supportedFourierSubspace (support : Finset Frequency) : Submodule ℂ FourierSpace :=
  supportedCoordinates (fieldSupport support)

theorem mem_supportedFourierSubspace (support : Finset Frequency) (x : FourierSpace) :
    x ∈ supportedFourierSubspace support ↔ ∀ f, f ∉ support → ∀ j, x (j,f) = 0 := by
  change (∀ e, e ∉ Finset.univ.product support → x e = 0) ↔ _
  constructor
  · intro hx f hf j
    exact hx (j,f) (by simpa using hf)
  · intro hx e he
    exact hx e.2 (by simpa using he) e.1

theorem supportedFourierSubspace_finrank (support : Finset Frequency) :
    Module.finrank ℂ (supportedFourierSubspace support) = 3*support.card := by
  rw [supportedFourierSubspace, supportedCoordinates_finrank]
  simp [fieldSupport, Fintype.card_fin]

abbrev HighCoordinates (low : Finset Frequency) := supportedFourierSubspace lowᶜ

theorem frequency_card : Fintype.card Frequency = 2000 := by
  simp [Frequency, Cell]

theorem highCoordinates_finrank (low : Finset Frequency) :
    Module.finrank ℂ (HighCoordinates low) = 3*(2000-low.card) := by
  rw [supportedFourierSubspace_finrank, Finset.card_compl, frequency_card]

def highEmbedding (low : Finset Frequency) : HighCoordinates low →ₗᵢ[ℂ] FourierSpace :=
  (supportedFourierSubspace lowᶜ).subtypeₗᵢ

theorem highEmbedding_restriction (low : Finset Frequency) (k : HighCoordinates low) :
    frequencyRestriction lowᶜ (highEmbedding low k) = highEmbedding low k := by
  ext e
  change (if e.2 ∈ lowᶜ then (k : FourierSpace) e else 0) = (k : FourierSpace) e
  split_ifs with he
  · rfl
  · exact ((mem_supportedFourierSubspace lowᶜ k).mp k.property e.2 he e.1).symm

theorem highEmbedding_support (low : Finset Frequency) (k : HighCoordinates low)
    (f : Frequency) (hf : f ∈ low) (j : Direction) : highEmbedding low k (j,f) = 0 :=
  (mem_supportedFourierSubspace lowᶜ k).mp k.property f (by simpa using hf) j

def highWeightedEmbedding (low : Finset Frequency) (c : Momentum)
    (w : Frequency → ℝ) (a : ℝ) : HighCoordinates low →ₗ[ℂ] WeightedSpace :=
  (weightedParts c w a).comp (highEmbedding low).toLinearMap

theorem highWeightedEmbedding_injective (low : Finset Frequency) (c : Momentum)
    (w : Frequency → ℝ) (a : ℝ) (hw : ∀ f, 0 < w f) (ha : 0 < a) :
    Function.Injective (highWeightedEmbedding low c w a) :=
  (weightedParts_injective c w a hw ha).comp (highEmbedding low).injective

/-- The actual unrestricted high-frequency coordinates retain the
frequency-dependent coercivity used in the weighted Schur trial. -/
theorem highWeightedEmbedding_auxiliary_lower
    (material : Cell20 → ℝ) (c : Momentum) (low : Finset Frequency) (ρ t t' : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (hw : ∀ f ∈ lowᶜ, 0 < laplacianSymbol c f/ρ-t') (ha : 0 < 2*t-t')
    (k : HighCoordinates low) :
    ‖highWeightedEmbedding low c (highWeight lowᶜ c ρ t') (2*t-t') k‖^2 ≤
      (inner ℂ (highEmbedding low k)
        ((auxiliaryMagneticFourier material c t t').toEuclideanLin (highEmbedding low k))).re := by
  have h := auxiliary_high_weighted_lower material c lowᶜ ρ t t' hm hw ha (highEmbedding low k)
  rw [highEmbedding_restriction] at h
  exact h

theorem highWeightedEmbedding_actual_injective (low : Finset Frequency) (c : Momentum)
    (ρ t t' : ℝ) (hw : ∀ f ∈ lowᶜ, 0 < laplacianSymbol c f/ρ-t') (ha : 0 < 2*t-t') :
    Function.Injective (highWeightedEmbedding low c (highWeight lowᶜ c ρ t') (2*t-t')) :=
  highWeightedEmbedding_injective low c _ _ (highWeight_pos lowᶜ c ρ t' hw) ha

theorem box_dimension_sum (low : Finset Frequency) (hlow : 2 ≤ 2*low.card) :
    2+(2*low.card-2)+(low.card+3*(2000-low.card)) = 6000 := by
  have hcard := Finset.card_le_univ low
  rw [frequency_card] at hcard
  omega

theorem box_finrank_sum (low : Finset Frequency) (hlow : 2 ≤ 2*low.card) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) +
      (Module.finrank ℂ (EuclideanSpace ℂ (Fin (2*low.card-2))) +
        (Module.finrank ℂ (LowGradientCoordinates low) +
          Module.finrank ℂ (HighCoordinates low))) = Module.finrank ℂ FourierSpace := by
  rw [lowGradientCoordinates_finrank, highCoordinates_finrank]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hf : Fintype.card Electric = 6000 := by simp [Electric, Cell]
  rw [hf]
  have h := box_dimension_sum low hlow
  omega

theorem box_finrank_sum_of_dimensions
    {N P : Type*} [AddCommGroup N] [Module ℂ N] [AddCommGroup P] [Module ℂ P]
    (low : Finset Frequency) (hlow : 2 ≤ 2*low.card)
    (hN : Module.finrank ℂ N = 2) (hP : Module.finrank ℂ P = 2*low.card-2) :
    Module.finrank ℂ N + (Module.finrank ℂ P +
      (Module.finrank ℂ (LowGradientCoordinates low) + Module.finrank ℂ (HighCoordinates low))) =
        Module.finrank ℂ FourierSpace := by
  rw [hN, hP]
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using box_finrank_sum low hlow

end Maxwell.Spectral.BoxCoordinates
