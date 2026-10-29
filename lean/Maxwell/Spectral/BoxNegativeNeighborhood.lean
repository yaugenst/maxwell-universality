import Maxwell.Spectral.BoxNeighborhood
import Maxwell.Spectral.MagneticThreshold

/-! Negative-only box certificates for the clean global cover. -/

noncomputable section

namespace Maxwell.Spectral.BoxNegativeNeighborhood

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxMagnetic BoxProjectionAssembly BoxLinear
open BoxNeighborhood

/-- Only the scalar checks needed by the two negative trial columns. -/
structure NegativeAccepted (b : Constants) : Prop where
  half_nonneg : ∀ j, 0 ≤ b.half j
  size_nonneg : 0 ≤ b.s
  size_bound : BoxSymbols.phaseScale*BoxSymbols.momentumNorm b.half ≤ b.s
  small_low : b.s < b.r
  sigma_nonneg : 0 ≤ b.σ
  sigma_small : b.σ < 1/64
  negative : b.negativeLoss < b.P0

/-- Actual center data for the negative columns, without positive columns,
high-space assumptions, or a material upper bound. -/
structure NegativeCenterBounds (material : Cell20 → ℝ) (c : Momentum)
    (b : Constants) (Fn : NegativeCoordinates →L[ℂ] Field) : Prop where
  symbol_low : ∀ f, b.r ≤ ‖longitudinalVector c f‖
  negative_transverse : ∀ x, Fn x ∈ transverseSubspace c
  negative_norm : ‖Fn‖ ≤ b.fn 0
  negative_curl : ‖appliedCurl c Fn‖ ≤ b.en 0
  negative_center : ∀ x,
    (inner ℂ x (compression material c (1/64) Fn Fn x)).re ≤ -b.P0*‖x‖^2
  negative_derivative : ∀ j, ‖firstCompression material c (axis j) Fn Fn‖ ≤ b.kn 0 j
  negative_weight : ∀ x,
    ‖scalarWeight (fun f => 1/‖longitudinalVector c f‖) (Fn x)‖^2 ≤ b.wn*‖x‖^2

theorem NegativeAccepted.of_full {b : Constants} (h : Accepted b) : NegativeAccepted b :=
  ⟨h.half_nonneg, h.size_nonneg, h.size_bound, h.small_low,
    h.sigma_nonneg, h.sigma_small, by linarith [h.negative]⟩

theorem NegativeCenterBounds.of_full {material : Cell20 → ℝ} {c : Momentum}
    {low : Finset Frequency} {b : Constants} {Fn : NegativeCoordinates →L[ℂ] Field}
    {Fp : PositiveCoordinates low →L[ℂ] Field} (h : CenterBounds material c low b Fn Fp) :
    NegativeCenterBounds material c b Fn :=
  ⟨h.symbol_low, h.negative_transverse, h.negative_norm, h.negative_curl,
    h.negative_center, h.negative_derivative, h.negative_weight⟩

variable {material : Cell20 → ℝ} {c : Momentum} {b : Constants}
variable {Fn : NegativeCoordinates →L[ℂ] Field}

/-- The exact two-column quadratic form is strictly negative throughout
the Cartesian box and the accepted frequency interval. -/
theorem negative_form (hb : NegativeAccepted b) (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ)
    (x : NegativeCoordinates) (hx : x ≠ 0) :
    (inner ℂ (Fn x)
      ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin (Fn x))).re < 0 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have h := BoxLowForms.negative_low_form material hm c q (1/64) t' Fn
    b.P0 b.s b.r (b.fn 0) (b.en 0) (b.dot (b.kn 0)) b.wn b.σ
    (by norm_num) hb.size_nonneg hq hb.small_low hc.symbol_low hc.negative_norm hc.negative_curl
    (firstCompression_box_bound material c q Fn Fn b.half (b.kn 0) hbox hc.negative_derivative)
    hshift hc.negative_transverse hc.negative_weight hc.negative_center x
  have hn : -b.P0+b.dot (b.kn 0)+b.s^2*(b.fn 0*b.en 0+(b.fn 0)^2)+
      2*(1/64)*b.s^2*b.wn/(1-b.s/b.r)^2+b.σ*(b.fn 0)^2 < 0 := by
    have hh := hb.negative
    unfold Constants.negativeLoss at hh
    linarith
  exact h.trans_lt (mul_neg_of_neg_of_pos hn (sq_pos_of_pos (norm_pos_iff.mpr hx)))

/-- Strict negativity proves independence of the two columns; it is not
an extra finite-certificate premise. -/
theorem negative_injective (hb : NegativeAccepted b) (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) : Function.Injective Fn := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  have h := negative_form hb hc hm 0 (1/64) (by simpa using hb.half_nonneg)
    (by simpa using hb.sigma_nonneg) (x-y) hne
  have hz : Fn (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  simp [hz] at h

theorem auxiliary_negative_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    2 ≤ (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t').eigenvalues rfl i < 0).card := by
  have h := finrank_le_card_negative_of_trial
    (auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
    (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t') Fn.toLinearMap
    (negative_form hb hc hm q t' hbox hshift)
  simpa only [NegativeCoordinates, finrank_euclideanSpace, Fintype.card_fin] using h

theorem transverse_negative_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    2 ≤ (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material (c+q) t').eigenvalues rfl i < 0).card := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  have ha : 0 < 2*(1/64)-t' := by
    have hs := (abs_le.mp hshift).2
    linarith [hb.sigma_small]
  rw [← auxiliaryMagneticFourier_negative_count material (c+q) (1/64) t' ha hlap]
  exact auxiliary_negative_count hb hc hm q t' hbox hshift

/-- The 2000 actual longitudinal modes add to the two certified transverse
negative directions at every accepted positive frequency. -/
theorem magnetic_negative_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    2002 ≤ (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material (c+q) t').eigenvalues rfl i < 0).card := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  have ht : 0 < t' := by
    have hs := (abs_le.mp hshift).1
    linarith [hb.sigma_small]
  rw [shiftedMagneticFourier_negative_count material (c+q) t' ht hlap]
  have h := transverse_negative_count hb hc hm q t' hbox hshift
  omega

/-- Actual electric inertia follows by the positive-mass Schur identity,
with no material upper bound or supplied spectral conclusion. -/
theorem electric_negative_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    2002 ≤ (Finset.univ.filter fun i =>
      (MagneticThreshold.electric_symmetric material (boundaryMomentum (c+q)) t').eigenvalues rfl i < 0).card := by
  have ht : 0 < t' := by
    have hs := (abs_le.mp hshift).1
    linarith [hb.sigma_small]
  rw [MagneticThreshold.electric_threshold_negative_count material (c+q) t' ht
    (fun e => lt_of_lt_of_le (by norm_num) (hm e))]
  exact magnetic_negative_count hb hc hm q t' hbox hshift

theorem reduced_frequency_electric_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum)
    (hbox : ∀ j, |q j| ≤ b.half j) :
    2002 ≤ (Finset.univ.filter fun i =>
      (MagneticThreshold.electric_symmetric material (boundaryMomentum (c+q))
        (1/64-b.σ)).eigenvalues rfl i < 0).card := by
  apply electric_negative_count hb hc hm q _ hbox
  rw [show (1/64-b.σ)-1/64 = -b.σ by ring, abs_neg, abs_of_nonneg hb.sigma_nonneg]

/-- The same clean certificate puts at least 2002 actual physical electric
eigenvalues strictly below minus the certified energy margin. -/
theorem electric_energy_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum)
    (hbox : ∀ j, |q j| ≤ b.half j) :
    2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum (c+q))).eigenvalues rfl i < -b.σ).card := by
  have hshift : |(1/64-b.σ)-1/64| ≤ b.σ := by
    rw [show (1/64-b.σ)-1/64 = -b.σ by ring, abs_neg, abs_of_nonneg hb.sigma_nonneg]
  exact (magnetic_negative_count hb hc hm q (1/64-b.σ) hbox hshift).trans
    (MagneticThreshold.energy_threshold_lower material hm (c+q) b.σ hb.sigma_nonneg hb.sigma_small)

theorem electric_physical_negative_count (hb : NegativeAccepted b)
    (hc : NegativeCenterBounds material c b Fn)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum)
    (hbox : ∀ j, |q j| ≤ b.half j) :
    2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum (c+q))).eigenvalues rfl i < 0).card := by
  apply (electric_energy_count hb hc hm q hbox).trans
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le (neg_nonpos.mpr hb.sigma_nonneg)

end Maxwell.Spectral.BoxNegativeNeighborhood
