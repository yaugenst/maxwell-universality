import Maxwell.Green.CalibrationPrecision
import Maxwell.Defect.EffectiveCompression
import Maxwell.Defect.DyadicSqrt

/-! Binary accuracy for the actual weighted compression using bounded
square-root bisection and the compact inverse-polynomial implementation. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000
variable {n : ℕ}

def binaryCompressionMatrix (edges : Fin n ↪ Edge) (m : Edge → ℚ) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (W : Fin n → ℚ) (b : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  rationalWeightedMatrix (compactCompression (coordinateBasis edges) m z ((M ^ 2)⁻¹)
    (precisionDegree δ M hδ hM hδM b)) (fun i => DyadicSqrt.weight (W i) b)

theorem binaryCompressionMatrix_error (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) (b : ℕ) :
    ‖rationalOperator (binaryCompressionMatrix edges m z δ M hδ hM hδM W b) -
      weightedInverseCompression edges m K hK hm z W‖ ≤
      (1 + 2 * (δ : ℝ)⁻¹) * (1 / 2 : ℝ)^b := by
  let T := compactCompression (coordinateBasis edges) m z ((M ^ 2)⁻¹)
    (precisionDegree δ M hδ hM hδM b)
  let R := compressionOperator edges (Ring.inverse (operator m K hK hm z))
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have herror : ‖rationalOperator T - realPartOperator R‖ ≤ (1 / 2 : ℝ)^b := by
    rw [norm_sub_rev]
    exact (realPartOperator_error R T).trans
      (compactCompression_binary_error edges m K hK hm z δ M hδ hM hδM hnorm hgap b)
  have hRn : ‖realPartOperator R‖ ≤ (δ : ℝ)⁻¹ :=
    (realPartOperator_norm_le R).trans
      (compressionOperator_inverse_norm_le edges m K hK hm z δ hδr hgap)
  have hw := rational_weighted_compression_error W (fun i => DyadicSqrt.weight (W i) b)
    (((2 : ℚ)^b)⁻¹) T (realPartOperator R) ((1 / 2 : ℝ)^b) (δ : ℝ)⁻¹
    hW hW1 (by positivity) (fun i => DyadicSqrt.weight_spec (W i) (hW i) (hW1 i) b) herror hRn
  convert hw using 1
  · rfl
  · simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, one_div, inv_pow]
    ring

theorem binaryCompressionMatrix_symmetric (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (W : Fin n → ℚ) (b : ℕ) :
    (binaryCompressionMatrix edges m z δ M hδ hM hδM W b).IsSymm := by
  apply rationalWeightedMatrix_isSymm
  rw [compactCompression_eq _ m K hK hm]
  exact compression_symmetric m K hK hm z _ _ _

end Maxwell.Defect.FiniteStencil
