import Maxwell.Spectral.BoxLowForms
import Maxwell.Spectral.BoxCoordinates
import Maxwell.Spectral.BoxResidual
import Maxwell.Spectral.BoxResidualTransfer
import Maxwell.Spectral.BoxGradientResidual
import Maxwell.Spectral.BoxGeometry

namespace Maxwell.Spectral.BoxNeighborhoodGeneral

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxMagnetic BoxCoordinates BoxProjectionAssembly
open BoxHighCoercivity BoxWeightAssembly BoxResidual BoxLinear BoxMixedForm

noncomputable section

/-- Scalar bounds stored with a center witness. The field order separates
negative, positive and gradient columns exactly as in the finite verifier. -/
structure Constants where
  rho : ℝ
  half : Direction → ℝ
  P0 : ℝ
  s : ℝ
  r : ℝ
  rh : ℝ
  R : ℝ
  σ : ℝ
  fn : Fin 2 → ℝ
  en : Fin 2 → ℝ
  kn : Fin 2 → Direction → ℝ
  crossder : Direction → ℝ
  rhow : Fin 2 → Direction → ℝ
  wn : ℝ
  wp2 : ℝ
  qfn : ℝ
  qw : ℝ
  rzero : ℝ

def Constants.dot (b : Constants) (k : Direction → ℝ) : ℝ := ∑ j, b.half j*k j

def Constants.negativeLoss (b : Constants) : ℝ :=
  b.dot (b.kn 0)+b.s^2*(b.fn 0*b.en 0+(b.fn 0)^2)+
    2*(1/64)*b.s^2*b.wn/(1-b.s/b.r)^2+b.σ*(b.fn 0)^2

def Constants.positiveLoss (b : Constants) : ℝ :=
  b.dot (b.kn 1)+b.s^2*(b.fn 1*b.en 1+(b.fn 1)^2)+b.σ*(b.fn 1)^2

def Constants.gradientLoss (b : Constants) : ℝ := 2*b.s^2/b.r^2+64*b.σ

def Constants.cross (b : Constants) : ℝ :=
  b.dot b.crossder+b.s^2*(8*(b.en 1/2+b.fn 1)+
    16*(1/64)*projectionCrossCoefficient b.s b.r b.R*b.wp2)

def Constants.base (b : Constants) : ℝ := b.rh^2/b.rho-1/64

def Constants.shift (b : Constants) : ℝ := (b.rh-b.s)^2/b.rho-1/64-b.σ

def Constants.wmax (b : Constants) : ℝ := 1/Real.sqrt b.base

def Constants.curlmax (b : Constants) : ℝ := b.rh/Real.sqrt b.base

def Constants.chi (b : Constants) : ℝ := Real.sqrt (b.base/b.shift)

def Constants.positiveResidual (b : Constants) : ℝ :=
  b.chi*(b.wmax*b.rzero+b.dot (b.rhow 0)+b.s^2*
    (b.wmax*b.en 1/2+(b.curlmax/2+b.wmax)*b.fn 1+
      2*(1/64)*b.wmax*((b.rh/2+3+b.s/b.rh)/(b.rh-b.s)^2)*b.qfn)+b.σ*b.qw)

def Constants.gradientResidual (b : Constants) : ℝ :=
  b.chi*(b.dot (b.rhow 1)+b.s^2*((b.curlmax/2+b.wmax)*8))

def Constants.positiveEta (b : Constants) : ℝ :=
  b.positiveResidual^2+(1/64+b.σ)*b.s^2*b.qfn^2/(b.rh-b.s)^2

def Constants.gradientEta (b : Constants) : ℝ := b.gradientResidual^2

/-- These are finite scalar inequalities; no neighborhood spectral
statement or operator remainder is an acceptance premise. -/
structure Accepted (b : Constants) : Prop where
  rho_pos : 0 < b.rho
  half_nonneg : ∀ j, 0 ≤ b.half j
  size_nonneg : 0 ≤ b.s
  size_bound : BoxSymbols.phaseScale*BoxSymbols.momentumNorm b.half ≤ b.s
  small_low : b.s < b.r
  small_high : b.s < b.rh
  cutoff_nonneg : 0 ≤ b.R
  sigma_nonneg : 0 ≤ b.σ
  sigma_small : b.σ < 1/64
  base_pos : 0 < b.base
  shift_pos : 0 < b.shift
  negative : 0 < b.P0-b.negativeLoss
  positive : 0 < b.P0-b.positiveLoss-b.positiveEta
  gradient : 0 < 1-b.gradientLoss-b.gradientEta
  determinant : (b.cross+Real.sqrt (b.positiveEta*b.gradientEta))^2 <
    (b.P0-b.positiveLoss-b.positiveEta)*(1-b.gradientLoss-b.gradientEta)

abbrev NegativeCoordinates (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev PositiveCoordinates (n : ℕ) (low : Finset Frequency) := EuclideanSpace ℂ (Fin (2*low.card-n))

/-- The actual finite center matrices and their three coordinate derivatives.
Each field is a norm, inner-product or symbol inequality at the center. -/
structure CenterBounds (material : Cell20 → ℝ) (c : Momentum) (low : Finset Frequency)
    (n : ℕ) (b : Constants) (Fn : NegativeCoordinates n →L[ℂ] Field)
    (Fp : PositiveCoordinates n low →L[ℂ] Field) : Prop where
  low_count : n ≤ 2*low.card
  symbol_low : ∀ f, b.r ≤ ‖longitudinalVector c f‖
  symbol_high : ∀ f ∈ lowᶜ, b.rh ≤ ‖longitudinalVector c f‖
  symbol_cutoff : ∀ f ∈ low, ‖longitudinalVector c f‖ ≤ b.R
  negative_transverse : ∀ x, Fn x ∈ transverseSubspace c
  positive_transverse : ∀ x, Fp x ∈ transverseSubspace c
  negative_norm : ‖Fn‖ ≤ b.fn 0
  positive_norm : ‖Fp‖ ≤ b.fn 1
  negative_curl : ‖appliedCurl c Fn‖ ≤ b.en 0
  positive_curl : ‖appliedCurl c Fp‖ ≤ b.en 1
  negative_center : ∀ x, (inner ℂ x (compression material c (1/64) Fn Fn x)).re ≤ -b.P0*‖x‖^2
  positive_center : ∀ x, b.P0*‖x‖^2 ≤ (inner ℂ x (compression material c (1/64) Fp Fp x)).re
  negative_derivative : ∀ j, ‖firstCompression material c (axis j) Fn Fn‖ ≤ b.kn 0 j
  positive_derivative : ∀ j, ‖firstCompression material c (axis j) Fp Fp‖ ≤ b.kn 1 j
  negative_weight : ∀ x, ‖scalarWeight (fun f => 1/‖longitudinalVector c f‖) (Fn x)‖^2 ≤ b.wn*‖x‖^2
  positive_low_weight : ‖(scalarWeight (BoxGradient.lowInverseLaplacian c low)).comp Fp‖ ≤ b.wp2
  mixed_derivative : ∀ j, ‖mixedFirstCompression material c (axis j) (1/64) low Fp‖ ≤ b.crossder j
  positive_high : ‖(restrictOperator lowᶜ).comp Fp‖ ≤ b.qfn
  positive_high_weight : ‖(scalarWeight (inverseWeight lowᶜ c b.rho (1/64))).comp Fp‖ ≤ b.qw
  positive_residual : ‖(restrictOperator lowᶜ).comp (auxiliaryAction material c (1/64) (1/64) Fp)‖ ≤ b.rzero
  positive_residual_derivative : ∀ j,
    ‖(scalarWeight (inverseWeight lowᶜ c b.rho (1/64))).comp
      (firstAuxiliaryAction material c (axis j) (1/64) Fp)‖ ≤ b.rhow 0 j
  gradient_residual_derivative : ∀ j,
    ‖(scalarWeight (inverseWeight lowᶜ c b.rho (1/64))).comp
      (firstMagneticAction material c (axis j) (gradientOperator c low))‖ ≤ b.rhow 1 j

variable {material : Cell20 → ℝ} {c : Momentum} {low : Finset Frequency} {b : Constants}
variable {n : ℕ}
variable {Fn : NegativeCoordinates n →L[ℂ] Field} {Fp : PositiveCoordinates n low →L[ℂ] Field}

/-- The negative block stays strictly negative on every accepted displacement. -/
theorem negative_form (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) (x : NegativeCoordinates n) (hx : x ≠ 0) :
    (inner ℂ (Fn x) ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin (Fn x))).re < 0 := by
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

theorem positive_form (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) (x : PositiveCoordinates n low) :
    (b.P0-b.positiveLoss)*‖x‖^2 ≤
      (inner ℂ (Fp x) ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin (Fp x))).re := by
  have h := BoxLowForms.positive_low_form material hm c q (1/64) t' Fp b.P0 b.s
    (b.fn 1) (b.en 1) (b.dot (b.kn 1)) b.σ (by norm_num) hq hc.positive_norm hc.positive_curl
    (firstCompression_box_bound material c q Fp Fp b.half (b.kn 1) hbox hc.positive_derivative)
    hshift hc.positive_center x
  convert h using 1
  unfold Constants.positiveLoss
  ring

theorem mixed_form (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (x : PositiveCoordinates n low) (g : LowGradientCoordinates low) :
    |(inner ℂ (Fp x) ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
      (lowGradientEmbedding c low g))).re| ≤ b.cross*‖x‖*‖g‖ := by
  have h := auxiliary_mixed_form material hm c q (1/64) t' low Fp b.s b.r b.R
    (b.fn 1) (b.en 1) b.wp2 (b.dot b.crossder) (by norm_num) hb.size_nonneg hq hb.small_low
    (fun f _ => hc.symbol_low f) hc.symbol_cutoff hb.cutoff_nonneg hc.positive_norm hc.positive_curl
    hc.positive_transverse hc.positive_low_weight
    (mixedFirstCompression_box_bound material c q (1/64) low Fp b.half b.crossder hbox hc.mixed_derivative)
    x (lowCoefficientEmbedding low g)
  rw [lowCoefficientEmbedding_norm] at h
  exact h

theorem positive_residual (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) :
    ‖(scalarWeight (inverseWeight lowᶜ (c+q) b.rho t')).comp
      (auxiliaryAction material (c+q) (1/64) t' Fp)‖ ≤ b.positiveResidual :=
  moving_auxiliary_box_bound material hm c q b.rho (1/64) t' b.σ b.s b.rh
    (b.fn 1) (b.en 1) b.qfn b.qw b.rzero lowᶜ Fp hc.positive_transverse
    b.half (b.rhow 0) hbox hc.positive_residual_derivative hb.rho_pos (by norm_num)
    hb.sigma_nonneg hshift hb.size_nonneg hq hb.small_high hc.symbol_high hb.base_pos hb.shift_pos
    hc.positive_norm hc.positive_curl hc.positive_high hc.positive_high_weight hc.positive_residual

theorem gradient_residual (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) :
    ‖(scalarWeight (inverseWeight lowᶜ (c+q) b.rho t')).comp
      (auxiliaryAction material (c+q) (1/64) t' (gradientOperator c low))‖ ≤ b.gradientResidual := by
  have h := BoxGradientResidual.moving_gradient_box_bound material hm c q b.rho (1/64) t'
    b.σ b.s b.rh 8 0 low lowᶜ (disjoint_compl_left_iff.mpr le_rfl) b.half (b.rhow 1) hbox
    hc.gradient_residual_derivative hb.rho_pos (by norm_num) hb.sigma_nonneg hb.size_nonneg
    hq hb.small_high hc.symbol_high (by have h := (abs_le.mp hshift).2; linarith)
    hb.base_pos hb.shift_pos (le_refl _) (le_refl _)
  simpa only [Constants.gradientResidual, Constants.dot, Constants.chi, Constants.wmax,
    Constants.curlmax, Constants.base, Constants.shift, mul_zero, zero_div, zero_add] using h

theorem gradient_form (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hshift : |t'-1/64| ≤ b.σ)
    (g : LowGradientCoordinates low) :
    (1-b.gradientLoss)*‖g‖^2 ≤
      (inner ℂ (lowGradientEmbedding c low g)
        ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
          (lowGradientEmbedding c low g))).re :=
  lowGradientEmbedding_auxiliary_lower material (fun e => lt_of_lt_of_le (by norm_num) (hm e))
    c q low b.s b.r b.σ t' hb.size_nonneg hq (hb.size_nonneg.trans_lt hb.small_low)
    (fun f _ => hc.symbol_low f) (by have h := (abs_le.mp hshift).2; linarith) g

theorem positive_high_form (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) (ha : 0 < 2*(1/64)-t')
    (hw : ∀ f ∈ lowᶜ, 0 < laplacianSymbol (c+q) f/b.rho-t')
    (x : PositiveCoordinates n low) (y : HighCoordinates low) :
    |(inner ℂ (Fp x) ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
      (highEmbedding low y))).re| ≤ Real.sqrt b.positiveEta*‖x‖*
        ‖highWeightedEmbedding low (c+q) (highWeight lowᶜ (c+q) b.rho t') (2*(1/64)-t') y‖ := by
  have hR := positive_residual hb hc hm q t' hq hbox hshift
  apply BoxResidualTransfer.high_coupling_of_scalarWeight material c q lowᶜ b.rho (1/64) t'
    b.σ b.s b.rh b.positiveResidual b.qfn ‖x‖ ha
    (by have h := (abs_le.mp hshift).1; linarith) hb.size_nonneg (norm_nonneg x) hq
    hb.small_high hc.symbol_high hw (Fp x) (highEmbedding low y) (hc.positive_transverse x)
    ((mem_supportedFourierSubspace lowᶜ y).mp y.property)
  · exact (((restrictOperator lowᶜ).comp Fp).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hc.positive_high (norm_nonneg x))
  · exact (((scalarWeight (inverseWeight lowᶜ (c+q) b.rho t')).comp
      (auxiliaryAction material (c+q) (1/64) t' Fp)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg x))

theorem gradient_high_form (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e) (q : Momentum) (t' : ℝ)
    (hq : displacementSize q ≤ b.s) (hbox : ∀ j, |q j| ≤ b.half j)
    (hshift : |t'-1/64| ≤ b.σ) (ha : 0 < 2*(1/64)-t')
    (hw : ∀ f ∈ lowᶜ, 0 < laplacianSymbol (c+q) f/b.rho-t')
    (g : LowGradientCoordinates low) (y : HighCoordinates low) :
    |(inner ℂ (lowGradientEmbedding c low g)
      ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
        (highEmbedding low y))).re| ≤ Real.sqrt b.gradientEta*‖g‖*
          ‖highWeightedEmbedding low (c+q) (highWeight lowᶜ (c+q) b.rho t') (2*(1/64)-t') y‖ := by
  have h := BoxGradientResidual.gradient_high_coupling_of_scalarWeight material c (c+q)
    low lowᶜ (disjoint_compl_left_iff.mpr le_rfl) b.rho (1/64) t' b.gradientResidual ha hw
    (gradient_residual hb hc hm q t' hq hbox hshift)
    (lowCoefficientEmbedding low g) (highEmbedding low y)
    ((mem_supportedFourierSubspace lowᶜ y).mp y.property)
  rw [lowCoefficientEmbedding_norm] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Constants.gradientEta, Real.sqrt_sq_eq_abs]
  exact le_abs_self _

theorem positiveEta_nonneg (hb : Accepted b) : 0 ≤ b.positiveEta := by
  have hσ := hb.sigma_nonneg
  unfold Constants.positiveEta
  positivity

theorem cross_nonneg (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp) :
    0 ≤ b.cross := by
  have hd : 0 ≤ b.dot b.crossder := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hb.half_nonneg j) ((norm_nonneg _).trans (hc.mixed_derivative j))
  have he := (norm_nonneg _).trans hc.positive_curl
  have hf := (norm_nonneg _).trans hc.positive_norm
  have hw := (norm_nonneg _).trans hc.positive_low_weight
  have hp := projectionCrossCoefficient_nonneg b.s b.r b.R hb.size_nonneg hb.small_low hb.cutoff_nonneg
  unfold Constants.cross
  positivity

theorem box_finrank_sum_general (low : Finset Frequency) (n : ℕ) (hn : n ≤ 2*low.card) :
    Module.finrank ℂ (NegativeCoordinates n) +
      (Module.finrank ℂ (PositiveCoordinates n low) +
        (Module.finrank ℂ (LowGradientCoordinates low) +
          Module.finrank ℂ (HighCoordinates low))) = Module.finrank ℂ FourierSpace := by
  rw [lowGradientCoordinates_finrank, highCoordinates_finrank]
  simp only [NegativeCoordinates, PositiveCoordinates, finrank_euclideanSpace, Fintype.card_fin]
  have hf : Fintype.card Electric = 6000 := by simp [Electric, Cell]
  rw [hf]
  have hcard := Finset.card_le_univ low
  rw [frequency_card] at hcard
  omega

/-- Once the finite center bounds and scalar inequalities hold, the full
6000-dimensional auxiliary matrix has exactly `n` negative eigenvalues and
no zero eigenvalue. The estimates apply to every point of the box. -/
theorem inertia_of_center_bounds (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e ∧ PrimitiveYee.edgeAverage material e ≤ b.rho)
    (q : Momentum) (t' : ℝ) (hq : displacementSize q ≤ b.s)
    (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ)
    (hw : ∀ f ∈ lowᶜ, 0 < laplacianSymbol (c+q) f/b.rho-t') :
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t').eigenvalues rfl i < 0).card = n ∧
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t').eigenvalues rfl i = 0).card = 0 := by
  have ha : 0 < 2*(1/64)-t' := by
    have hs := (abs_le.mp hshift).2
    linarith [hb.sigma_small]
  have hηp := positiveEta_nonneg hb
  have hηg : 0 ≤ b.gradientEta := sq_nonneg _
  have hp : 0 < (b.P0-b.positiveLoss)-(Real.sqrt b.positiveEta)^2 := by
    rw [Real.sq_sqrt hηp]
    exact hb.positive
  have hg : 0 < (1-b.gradientLoss)-(Real.sqrt b.gradientEta)^2 := by
    rw [Real.sq_sqrt hηg]
    exact hb.gradient
  have hd : (b.cross+Real.sqrt b.positiveEta*Real.sqrt b.gradientEta)^2 <
      ((b.P0-b.positiveLoss)-(Real.sqrt b.positiveEta)^2)*
        ((1-b.gradientLoss)-(Real.sqrt b.gradientEta)^2) := by
    rw [Real.sq_sqrt hηp, Real.sq_sqrt hηg, ← Real.sqrt_mul hηp]
    exact hb.determinant
  have h := BoxSchur.inertia_of_box_trials
    (auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
    (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t')
    Fn.toLinearMap Fp.toLinearMap (lowGradientEmbedding c low).toLinearMap
    (highEmbedding low).toLinearMap
    (highWeightedEmbedding low (c+q) (highWeight lowᶜ (c+q) b.rho t') (2*(1/64)-t'))
    (highWeightedEmbedding_actual_injective low (c+q) b.rho (1/64) t' hw ha)
    (b.P0-b.positiveLoss) (1-b.gradientLoss) b.cross
    (Real.sqrt b.positiveEta) (Real.sqrt b.gradientEta)
    (cross_nonneg hb hc) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hp hg hd
    (negative_form hb hc (fun e => (hm e).1) q t' hq hbox hshift)
    (positive_form hc (fun e => (hm e).1) q t' hq hbox hshift)
    (gradient_form hb hc (fun e => (hm e).1) q t' hq hshift)
    (highWeightedEmbedding_auxiliary_lower material (c+q) low b.rho (1/64) t'
      (fun e => ⟨lt_of_lt_of_le (by norm_num) (hm e).1, (hm e).2⟩) hw ha)
    (mixed_form hb hc (fun e => (hm e).1) q t' hq hbox)
    (positive_high_form hb hc (fun e => (hm e).1) q t' hq hbox hshift ha hw)
    (gradient_high_form hb hc (fun e => (hm e).1) q t' hq hbox hshift ha hw)
    (box_finrank_sum_general low n hc.low_count)
  constructor
  · simpa only [NegativeCoordinates, finrank_euclideanSpace, Fintype.card_fin] using h.1
  · exact h.2.1

/-- All geometric and high-weight conditions are derived from the finite
symbol bounds. This is the finite-center-to-whole-box acceptance theorem. -/
theorem accepted_box_inertia (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e ∧ PrimitiveYee.edgeAverage material e ≤ b.rho)
    (q : Momentum) (t' : ℝ) (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t').eigenvalues rfl i < 0).card = n ∧
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material (c+q) (1/64) t').eigenvalues rfl i = 0).card = 0 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  exact inertia_of_center_bounds hb hc hm q t' hq hbox hshift
    (BoxGeometry.shifted_high_weight_pos c q lowᶜ b.rho (1/64) t' b.σ b.s b.rh
      hb.rho_pos hq hb.small_high hc.symbol_high
      (by have h := (abs_le.mp hshift).2; linarith) hb.shift_pos)

/-- The full auxiliary certificate determines the physical transverse
magnetic inertia at every energy in the accepted interval. -/
theorem accepted_box_transverse_inertia (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e ∧ PrimitiveYee.edgeAverage material e ≤ b.rho)
    (q : Momentum) (t' : ℝ) (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material (c+q) t').eigenvalues rfl i < 0).card = n ∧
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material (c+q) t').eigenvalues rfl i = 0).card = 0 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  have ha : 0 < 2*(1/64)-t' := by
    have hs := (abs_le.mp hshift).2
    linarith [hb.sigma_small]
  rw [← auxiliaryMagneticFourier_negative_count material (c+q) (1/64) t' ha hlap,
    ← auxiliaryMagneticFourier_zero_count material (c+q) (1/64) t' ha hlap]
  exact accepted_box_inertia hb hc hm q t' hbox hshift

theorem accepted_box_electric_count (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e ∧ PrimitiveYee.edgeAverage material e ≤ b.rho)
    (q : Momentum) (hbox : ∀ j, |q j| ≤ b.half j) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum (c+q))).eigenvalues rfl i < 0).card = n+2000 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  rw [electric_negative_count_eq_auxiliary_add_longitudinal material (c+q) (1/64)
    (fun e => lt_of_lt_of_le (by norm_num) (hm e).1) (by norm_num) hlap,
    (accepted_box_inertia hb hc hm q (1/64) hbox (by simpa using hb.sigma_nonneg)).1]

/-- The full magnetic count at either accepted frequency endpoint includes
the actual 2000 longitudinal directions. -/
theorem accepted_box_magnetic_count (hb : Accepted b) (hc : CenterBounds material c low n b Fn Fp)
    (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e ∧ PrimitiveYee.edgeAverage material e ≤ b.rho)
    (q : Momentum) (t' : ℝ) (hbox : ∀ j, |q j| ≤ b.half j) (hshift : |t'-1/64| ≤ b.σ) :
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material (c+q) t').eigenvalues rfl i < 0).card = n+2000 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  have ht : 0 < t' := by
    have hs := (abs_le.mp hshift).1
    linarith [hb.sigma_small]
  rw [shiftedMagneticFourier_negative_count material (c+q) t' ht hlap,
    (accepted_box_transverse_inertia hb hc hm q t' hbox hshift).1]

end
end Maxwell.Spectral.BoxNeighborhoodGeneral
