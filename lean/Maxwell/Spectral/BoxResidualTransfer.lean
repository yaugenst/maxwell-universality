import Maxwell.Spectral.BoxHighCoercivity
import Maxwell.Spectral.BoxWeightAssembly

/-! The stored scalar inverse-weight residual controls the exact dual
high-space norm used in the auxiliary Schur estimate. -/

noncomputable section

namespace Maxwell.Spectral.BoxResidualTransfer

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open BoxHighCoercivity BoxProjectionAssembly BoxWeightAssembly

/-- Outside the high set the restriction vanishes. On the high set the
dual square-root weight is precisely the stored scalar inverse weight. -/
theorem inverse_highWeight_restriction
    (support : Finset Frequency) (c : Momentum) (ρ t' : ℝ) (x : FourierSpace) :
    frequencyWeight (fun f => (Real.sqrt (highWeight support c ρ t' f))⁻¹)
      (frequencyRestriction support x) = scalarWeight (inverseWeight support c ρ t') x := by
  apply WithLp.ofLp_injective 2
  funext e
  change Complex.ofReal ((Real.sqrt (highWeight support c ρ t' e.2))⁻¹) *
    (if e.2 ∈ support then x e else 0) = Complex.ofReal (inverseWeight support c ρ t' e.2) * x e
  by_cases hf : e.2 ∈ support <;> simp [highWeight, inverseWeight, hf, one_div]

theorem inverse_highWeight_transverse_restriction
    (support : Finset Frequency) (c : Momentum) (ρ t' : ℝ) (x : FourierSpace) :
    frequencyWeight (fun f => (Real.sqrt (highWeight support c ρ t' f))⁻¹)
      (transversePart c (frequencyRestriction support x)) =
      scalarWeight (inverseWeight support c ρ t') (transversePart c x) := by
  rw [transversePart_restriction, inverse_highWeight_restriction]

/-- Passing to the moved transverse residual cannot enlarge the supplied
scalar-weighted residual bound. This does not require positive weights. -/
theorem transverse_residual_norm_le
    (support : Finset Frequency) (c : Momentum) (ρ t' : ℝ) (x : FourierSpace) :
    ‖frequencyWeight (fun f => (Real.sqrt (highWeight support c ρ t' f))⁻¹)
      (transversePart c (frequencyRestriction support x))‖ ≤
      ‖scalarWeight (inverseWeight support c ρ t') x‖ := by
  rw [inverse_highWeight_transverse_restriction]
  exact weighted_transversePart_norm_le c (inverseWeight support c ρ t') x

/-- The actual masked inverse-weight residual yields the complete dual
high norm, including the exactly controlled longitudinal leakage. -/
theorem residual_bound_of_scalarWeight
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c q : Momentum) (support : Finset Frequency) (ρ t t' σ s rh rw qfn M : ℝ)
    (ha : 0 < 2 * t - t') (ht' : t - σ ≤ t') (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hq : BoxSymbols.phaseScale * BoxSymbols.momentumNorm q ≤ s) (hsr : s < rh)
    (hr : ∀ f ∈ support, rh ≤ ‖longitudinalVector c f‖)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c)
    (hF : ‖frequencyRestriction support x‖ ≤ qfn * M)
    (hR : ‖scalarWeight (inverseWeight support (c + q) ρ t')
      ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin x)‖ ≤ rw * M) :
    ‖inverseWeightedParts (c + q) (highWeight support (c + q) ρ t') (2 * t - t')
      (frequencyRestriction support
        ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin x))‖ ≤
      Real.sqrt (rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2) * M := by
  exact inverseWeightedParts_residual_bound material c q support
    (highWeight support (c + q) ρ t') t t' σ s rh rw qfn M ha ht' hs hM hq hsr hr x hx hF
    ((transverse_residual_norm_le support (c + q) ρ t' _).trans hR)

/-- Final weighted high coupling directly from the scalar residual
certificate; its norm is exactly the norm in the high coercivity theorem. -/
theorem high_coupling_of_scalarWeight
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c q : Momentum) (support : Finset Frequency) (ρ t t' σ s rh rw qfn M : ℝ)
    (ha : 0 < 2 * t - t') (ht' : t - σ ≤ t') (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hq : BoxSymbols.phaseScale * BoxSymbols.momentumNorm q ≤ s) (hsr : s < rh)
    (hr : ∀ f ∈ support, rh ≤ ‖longitudinalVector c f‖)
    (hw : ∀ f ∈ support, 0 < laplacianSymbol (c + q) f / ρ - t')
    (x y : FourierSpace) (hx : x ∈ transverseSubspace c)
    (hy : ∀ f, f ∉ support → ∀ j, y (j, f) = 0)
    (hF : ‖frequencyRestriction support x‖ ≤ qfn * M)
    (hR : ‖scalarWeight (inverseWeight support (c + q) ρ t')
      ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin x)‖ ≤ rw * M) :
    |(inner ℂ x ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin y)).re| ≤
      Real.sqrt (rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2) * M *
        ‖weightedParts (c + q) (highWeight support (c + q) ρ t') (2 * t - t') y‖ := by
  exact auxiliary_high_coupling material (c + q) support (highWeight support (c + q) ρ t')
    t t' (Real.sqrt (rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2)) M
    (highWeight_pos support (c + q) ρ t' hw) ha x y hy
    (residual_bound_of_scalarWeight material c q support ρ t t' σ s rh rw qfn M
      ha ht' hs hM hq hsr hr x hx hF hR)

end Maxwell.Spectral.BoxResidualTransfer
