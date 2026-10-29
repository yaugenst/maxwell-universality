import Maxwell.Green.PlatformCalibration
import Maxwell.Green.PhysicalCompression

/-! Exact rational evaluation of translated scalar couplings, with a
binary error bound against the actual infinite lattice inverse. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
open scoped InnerProductSpace
set_option maxHeartbeats 600000

/-- A rational source, represented by its actual finite list of edges. -/
def rationalSource {n : ℕ} (edges : Fin n → Edge) (a : Fin n → ℚ) : SparseField :=
  List.ofFn fun i => (edges i, a i)

theorem embed_rationalSource {n : ℕ} (edges : Fin n → Edge) (a : Fin n → ℚ) :
    embed (rationalSource edges a) =
      Green.PhysicalCompression.finiteField edges (fun i => (a i : ℂ)) := by
  simp only [embed, rationalSource, List.map_ofFn, List.sum_ofFn,
    Green.PhysicalCompression.finiteField, Function.comp_apply]

/-- The finite polynomial has binary operator error before any source
compression, so separated and overlapping sources use the same evaluator. -/
theorem inversePolynomial_binary_error (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) (b : ℕ) :
    ‖Ring.inverse (operator m K hK hm z) -
      inversePolynomial (operator m K hK hm z) (((M ^ 2)⁻¹ : ℚ) : ℂ)
        (precisionDegree δ M hδ hM hδM b)‖ ≤ (1 / 2 : ℝ)^b := by
  let : IsometricContinuousFunctionalCalculus ℝ (Field →L[ℂ] Field) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let : Nontrivial Field := by
    refine ⟨⟨lp.single 2 ((0 : Direction), (0 : Site)) (1 : ℂ), 0, ?_⟩⟩
    intro h
    have he := congrArg (fun f : Field => f ((0 : Direction), (0 : Site))) h
    simp at he
  rw [← inversePolynomial_real_cast]
  have he := inversePolynomial_spectral_error (operator m K hK hm z)
    (operator_selfAdjoint m K hK hm z) (δ : ℝ) (M : ℝ)
    (precisionDegree δ M hδ hM hδM b) (by exact_mod_cast hδ)
    (by exact_mod_cast hM) (by exact_mod_cast hδM) hnorm hgap
  have hb := precisionDegree_error δ M hδ hM hδM b
  unfold inverseFactor at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr hb
  have hreal : (δ : ℝ)⁻¹ * (1 - (δ : ℝ)^2 / (M : ℝ)^2) ^
      (precisionDegree δ M hδ hM hδM b + 1) ≤ (1 / 2 : ℝ)^b := by
    simpa only [Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_sub, Rat.cast_one,
      Rat.cast_div, Rat.cast_ofNat] using hc
  convert he.trans hreal using 1
  simp only [Rat.cast_inv, Rat.cast_pow]
  rfl

/-- Exact rational output and its physical scalar error. -/
theorem compact_pairing_binary_error (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|)
    (u v : SparseField) (b : ℕ) :
    ‖(pairing u (compactInverseAction m z ((M ^ 2)⁻¹)
          (precisionDegree δ M hδ hM hδM b) v) : ℂ) -
      inner ℂ (embed u) (Ring.inverse (operator m K hK hm z) (embed v))‖ ≤
        (1 / 2 : ℝ)^b * ‖embed u‖ * ‖embed v‖ := by
  rw [pairing_inner, embed_compactInverseAction m K hK hm, ← inner_sub_right]
  have he := inversePolynomial_binary_error m K hK hm z δ M hδ hM hδM hnorm hgap b
  have hn : ‖inversePolynomial (operator m K hK hm z) (((M ^ 2)⁻¹ : ℚ) : ℂ)
      (precisionDegree δ M hδ hM hδM b) - Ring.inverse (operator m K hK hm z)‖ ≤
      (1 / 2 : ℝ)^b := by simpa only [norm_sub_rev] using he
  calc
    _ ≤ ‖embed u‖ * ‖(inversePolynomial (operator m K hK hm z) (((M ^ 2)⁻¹ : ℚ) : ℂ)
      (precisionDegree δ M hδ hM hδM b) - Ring.inverse (operator m K hK hm z)) (embed v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖embed u‖ * ((1 / 2 : ℝ)^b * ‖embed v‖) := by
      exact mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))
        (norm_nonneg _)
    _ = _ := by ring

end Maxwell.Defect.FiniteStencil

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression
open scoped InnerProductSpace
set_option maxHeartbeats 600000

def rationalCoupling {N : ℕ} (P : PhysicalPlatform) (edges : Fin N → Edge)
    (a : Fin N → ℚ) (n : Site) (b : ℕ) : ℚ :=
  pairing (rationalSource edges a)
    (compactInverseAction P.rationalMaterial 0 ((P.rowBound ^ 2)⁻¹) (P.calibrationDegree b)
      (rationalSource (translateEdge n ∘ edges) a))

theorem rationalCoupling_error {N : ℕ} (P : PhysicalPlatform) (edges : Fin N ↪ Edge)
    (a : Fin N → ℚ) (n : Site) (b : ℕ) :
    ‖(P.rationalCoupling edges a n b : ℂ) -
      scalarCoupling edges (fun i => (a i : ℂ)) (P.bulk.symm : Field →L[ℂ] Field) n‖ ≤
        (1 / 2 : ℝ)^b * ‖(WithLp.toLp 2 (fun i => (a i : ℂ)) : EuclideanSpace ℂ (Fin N))‖^2 := by
  have he := compact_pairing_binary_error P.rationalMaterial 25 (by norm_num)
    P.rationalMaterial_bound 0 P.calibrationGap P.rowBound P.calibrationGap_pos
    P.rowBound_pos P.calibrationGap_le P.calibration_norm_bound P.calibration_spectral_gap
    (rationalSource edges a) (rationalSource (translateEdge n ∘ edges) a) b
  rw [P.rationalOperator_binding, ← PeriodicScalarBackground.bulk_inverse_eq P] at he
  rw [embed_rationalSource, embed_rationalSource] at he
  let aC : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun i => (a i : ℂ))
  have hnorm (f : Fin N ↪ Edge) : ‖finiteField f aC‖ = ‖aC‖ := by
    change ‖Maxwell.Target.sequenceExtension f aC‖ = ‖aC‖
    exact (Maxwell.Target.sequenceExtension f).norm_map aC
  change ‖(P.rationalCoupling edges a n b : ℂ) -
    inner ℂ (finiteField edges aC) (P.bulk.symm (finiteField (translatedEmbedding edges n) aC))‖ ≤
    (1 / 2 : ℝ)^b * ‖aC‖^2
  change ‖(P.rationalCoupling edges a n b : ℂ) -
    inner ℂ (finiteField edges aC) (P.bulk.symm (finiteField (translatedEmbedding edges n) aC))‖ ≤
    (1 / 2 : ℝ)^b * ‖finiteField edges aC‖ * ‖finiteField (translatedEmbedding edges n) aC‖ at he
  rw [hnorm edges, hnorm (translatedEmbedding edges n)] at he
  simpa only [pow_two, mul_assoc] using he

end Maxwell.Composition.PhysicalPlatform
