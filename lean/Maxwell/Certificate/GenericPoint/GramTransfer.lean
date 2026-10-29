import Maxwell.Certificate.GenericPoint.JetStructure
import Maxwell.Certificate.CurvatureTransferGeneric
import Maxwell.Certificate.QuadraticTransfer

/-! Transfer arbitrary checked six-by-six Hessian and full residual Gram
data to the actual exact spectral frame at any primitive TRIM. The error
inputs are proved from saved-vector residuals by `GenericPoint.VerifiedBounds`. -/
namespace Maxwell.Certificate.GenericPoint.Data

open Matrix Maxwell.Spectral Maxwell.Spectral.YeeTaylor
open Maxwell.Certificate.CurvatureTransfer Maxwell.Certificate.QuadraticTransfer
noncomputable section

theorem contraction_relative_generic
    (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] Space)
    (G H : Matrix (Fin 6) (Fin 6) ℝ)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hrelative : ((9/5 : ℝ) • H-G-
      (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖contraction W q x‖^2 ≤ (18/5 : ℝ)*radius q^2*
      Complex.re (inner ℂ x (directionalHalf H q x))-
        (1/10000 : ℝ)*radius q^4*‖x‖^2 := by
  have hr := matrix_relative_bound G H (9/5) (1/10000)
    hrelative (CorrectorWitness.directionCoefficients q x)
  rw [CorrectorWitness.directionCoefficients_norm_sq] at hr
  have h := (contraction_sq_le W G hgram q x).trans
    (mul_le_mul_of_nonneg_left hr (sq_nonneg _))
  rw [directionalHalf_quadratic]
  nlinarith only [h]

variable (D : GenericPoint.Data)

theorem rounded_coefficient_error (hgap : D.ComplementGap) (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (H G : Matrix (Fin 6) (Fin 6) ℝ)
    (hentry : ∀ i j, |G i j-H i j| ≤ 1/10^11)
    (hbinding : D.savedEffectiveCoefficient q savedY = directionalHalf G q)
    (herror : ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤
      (1/1000000 : ℝ)*radius q^2) :
    ‖D.effectiveCoefficient hgap q-directionalHalf H q‖ ≤
      (2/1000000 : ℝ)*radius q^2 := by
  have hr := directionalHalf_error G H q (1/10^11) (by positivity) hentry
  rw [hbinding] at herror
  have ht := norm_sub_le_norm_sub_add_norm_sub (D.effectiveCoefficient hgap q)
    (directionalHalf G q) (directionalHalf H q)
  nlinarith [sq_nonneg (radius q)]

theorem residualGram_of_finite (hgap : D.ComplementGap) (q : PeriodicYee.Momentum)
    (S : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] Space)
    (G H : Matrix (Fin 6) (Fin 6) ℝ)
    (hbinding : S = contraction W q)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hupper : ((4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)-G).PosSemidef)
    (hrelative : ((9/5 : ℝ) • H-G-
      (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hRerror : ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1-S‖ ≤
      (1/1000000 : ℝ)*radius q^2)
    (hKerror : ‖D.effectiveCoefficient hgap q-directionalHalf H q‖ ≤
      (2/1000000 : ℝ)*radius q^2) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1 x‖^2 ≤
      (18/5 : ℝ)*radius q^2*Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) := by
  apply QuadraticResidual.relative_bound_of_saved _ S _ (directionalHalf H q)
    (radius q) _ hRerror hKerror _ x
  · rw [hbinding]
    exact contraction_norm_le W G hgram hupper q
  · intro y
    rw [hbinding]
    exact contraction_relative_generic W G H hgram hrelative q y

/-- Finite matrix inequalities and their exact operator bindings yield the
full local jet package. Every approximation error has an independently
proved residual-based producer in `VerifiedBounds`. -/
theorem finiteJetBounds_of_finite (hgap : D.ComplementGap)
    (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (q : PeriodicYee.Momentum) (hwidth : D.width ≤ 7/256-D.energy)
    (savedY S : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] Space)
    (H Happrox G : Matrix (Fin 6) (Fin 6) ℝ)
    (hlo : (H-(2003/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hhi : ((49997/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)-H).PosSemidef)
    (hentry : ∀ i j, |Happrox i j-H i j| ≤ 1/10^11)
    (hKbinding : D.savedEffectiveCoefficient q savedY = directionalHalf Happrox q)
    (hSbinding : S = contraction W q)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hupper : ((4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)-G).PosSemidef)
    (hrelative : ((9/5 : ℝ) • H-G-
      (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hKerror : ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤
      (1/1000000 : ℝ)*radius q^2)
    (hRerror : ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1-S‖ ≤
      (1/1000000 : ℝ)*radius q^2) :
    FiniteJetBounds (D.taylorCoefficient q) (D.exactIsometry hgap).toContinuousLinearMap
      (D.corrector hgap q) (radius q) D.width D.energy := by
  have hrounded := D.rounded_coefficient_error hgap q savedY H Happrox hentry hKbinding hKerror
  have hreplace : ‖D.effectiveCoefficient hgap q-directionalHalf Happrox q‖ ≤
      (1/1000000 : ℝ)*radius q^2 := by simpa only [hKbinding] using hKerror
  apply D.finiteJetBounds hgap σ hσ hv q hwidth
  · exact CurvatureTransferGeneric.directional_bounds_of_approximation
      H Happrox hlo hhi q (D.effectiveCoefficient hgap q) hentry hreplace
  · exact D.residualGram_of_finite hgap q S W G H hSbinding hgram hupper hrelative hRerror hrounded

/-- The complete local-band exclusion endpoint for an arbitrary checked
L-point data set, with the same finite Hessian and tensor Gram bindings. -/
theorem local_band_gap_of_finite (hgap : D.ComplementGap)
    (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (q : PeriodicYee.Momentum) (hr0 : 0 < radius q) (hr : radius q ≤ 1/20)
    (hw : D.width ≤ 1/2^20) (hEl : 239/25000 ≤ D.energy) (hEu : D.energy ≤ 957/100000)
    (hY : ‖D.corrector hgap q‖ ≤ 3*radius q)
    (savedY S : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (W : Fin 3 → EuclideanSpace ℂ (Fin 6) →L[ℂ] Space)
    (H Happrox G : Matrix (Fin 6) (Fin 6) ℝ)
    (hlo : (H-(2003/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hhi : ((49997/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)-H).PosSemidef)
    (hentry : ∀ i j, |Happrox i j-H i j| ≤ 1/10^11)
    (hKbinding : D.savedEffectiveCoefficient q savedY = directionalHalf Happrox q)
    (hSbinding : S = contraction W q)
    (hgram : ∀ z, ∑ i, ‖W i z‖^2 ≤ Complex.re (inner ℂ z (realMatrixOperator G z)))
    (hupper : ((4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)-G).PosSemidef)
    (hrelative : ((9/5 : ℝ) • H-G-
      (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)).PosSemidef)
    (hKerror : ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤
      (1/1000000 : ℝ)*radius q^2)
    (hRerror : ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1-S‖ ≤
      (1/1000000 : ℝ)*radius q^2)
    (hinertia : (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256).card ≤ 2) :
    ∀ i : Index, 0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i →
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256 →
      radius q^2/600 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i-D.energy := by
  have hwidth : D.width ≤ 7/256-D.energy := by linarith
  apply YeeLocal.local_band_gap D.k q D.width D.energy
    (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q)
    hr0 hr D.width_pos.le hw hEl hEu (D.exactIsometry hgap).norm_toContinuousLinearMap_le hY
    (D.corrector_equation hgap σ hσ hv q) σ hσ
    (D.exactIsometry_parity hgap σ hv) (D.corrector_parity hgap σ hσ hv q)
    (D.finiteJetBounds_of_finite hgap σ hσ hv q hwidth savedY S W H Happrox G
      hlo hhi hentry hKbinding hSbinding hgram hupper hrelative hKerror hRerror) _ hinertia
  simp

end
end Maxwell.Certificate.GenericPoint.Data
