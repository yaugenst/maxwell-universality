import Maxwell.Spectral.BoxCrossNorm
import Maxwell.Spectral.BoxCompression

/-! Actual magnetic Fourier compressions satisfy the box Taylor bounds.
The material inverse, curl increments and linear remainder are the concrete
operators already bound to the primitive Yee model. -/

noncomputable section

namespace Maxwell.Spectral.BoxMagnetic

set_option maxRecDepth 4000

open Matrix Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open BoxCompression BoxCrossNorm
open scoped Matrix.Norms.L2Operator

abbrev Field := EuclideanSpace ℂ Electric

private theorem matrix_adjoint (M : Matrix Electric Electric ℂ) :
    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) M.conjTranspose =
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) M).adjoint := by
  change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (star M) =
    star (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) M)
  exact map_star _ M

def inverseMaterial (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) : Field →L[ℂ] Field :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (fourierInverseMass material)

theorem inverseMass_norm (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) :
    ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (inverseMass material)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, inverseMass, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro e
  have he : 0 < edgeAverage material e := lt_of_lt_of_le zero_lt_one (hm e)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  simpa only [one_div] using (div_le_one he).mpr (hm e)

theorem electricTransform_norm (c : Momentum) :
    ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform c)‖ ≤ 1 := by
  let U := Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform c)
  have hu : U.adjoint.comp U = 1 := by
    change star U * U = 1
    dsimp [U]
    rw [← map_star, ← map_mul]
    change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      ((electricTransform c).conjTranspose * electricTransform c) = 1
    rw [electricTransform_conjTranspose_mul, map_one]
  have hn := ContinuousLinearMap.norm_adjoint_comp_self U
  rw [hu, norm_one] at hn
  change ‖U‖ ≤ 1
  nlinarith [norm_nonneg U]

theorem inverseMaterial_norm (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) : ‖inverseMaterial material‖ ≤ 1 := by
  unfold inverseMaterial fourierInverseMass
  rw [map_mul, map_mul, matrix_adjoint]
  calc
    _ ≤ ‖star (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform 0))‖ *
        ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (inverseMass material)‖ *
        ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform 0)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 := by
      change ‖(Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform 0)).adjoint‖ *
        ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (inverseMass material)‖ *
        ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (electricTransform 0)‖ ≤ 1
      rw [ContinuousLinearMap.adjoint.norm_map]
      have hU := electricTransform_norm (0 : Momentum)
      have hD := inverseMass_norm material hm
      have hab := mul_le_mul hU hD (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have habc := mul_le_mul hab hU (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1*1)
      simpa only [one_mul] using habc

def curlOperator (c : Momentum) : Field →L[ℂ] Field :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (frequencyCurl c)

def linearCurlOperator (c q : Momentum) : Field →L[ℂ] Field :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (linearFrequencyCurl c q)

def displacementSize (q : Momentum) : ℝ := BoxSymbols.phaseScale * BoxSymbols.momentumNorm q

theorem displacementSize_nonneg (q : Momentum) : 0 ≤ displacementSize q :=
  mul_nonneg BoxSymbols.phaseScale_pos.le (norm_nonneg _)

theorem curlOperator_increment (c q : Momentum) :
    ‖curlOperator (c + q) - curlOperator c‖ ≤ displacementSize q := by
  simpa only [curlOperator, map_sub, displacementSize] using frequencyCurl_increment_norm c q

theorem curlOperator_remainder (c q : Momentum) :
    ‖curlOperator (c + q) - curlOperator c - linearCurlOperator c q‖ ≤
      displacementSize q^2/2 := by
  simpa only [curlOperator, linearCurlOperator, map_sub, displacementSize, mul_pow] using
    frequencyCurl_linear_remainder_norm c q

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def appliedCurl (c : Momentum) (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (curlOperator c).adjoint.comp F

def appliedLinear (c q : Momentum) (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (linearCurlOperator c q).adjoint.comp F

def appliedIncrement (c q : Momentum) (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (curlOperator (c+q) - curlOperator c).adjoint.comp F

theorem appliedCurl_add (c q : Momentum) (F : V →L[ℂ] Field) :
    appliedCurl (c+q) F = appliedCurl c F + appliedIncrement c q F := by
  simp only [appliedCurl, appliedIncrement, map_sub, ContinuousLinearMap.sub_comp]
  module

theorem appliedIncrement_norm (c q : Momentum) (F : V →L[ℂ] Field)
    (ν : ℝ) (hF : ‖F‖ ≤ ν) :
    ‖appliedIncrement c q F‖ ≤ displacementSize q * ν := by
  calc
    _ ≤ ‖(curlOperator (c+q) - curlOperator c).adjoint‖ * ‖F‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖curlOperator (c+q) - curlOperator c‖ * ‖F‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul (curlOperator_increment c q) hF (norm_nonneg _)
      (displacementSize_nonneg q)

theorem appliedRemainder_norm (c q : Momentum) (F : V →L[ℂ] Field)
    (ν : ℝ) (hF : ‖F‖ ≤ ν) :
    ‖appliedIncrement c q F - appliedLinear c q F‖ ≤ displacementSize q^2 * ν / 2 := by
  have he : appliedIncrement c q F - appliedLinear c q F =
      (curlOperator (c+q) - curlOperator c - linearCurlOperator c q).adjoint.comp F := by
    simp only [appliedIncrement, appliedLinear, map_sub, ContinuousLinearMap.sub_comp]
  rw [he]
  calc
    _ ≤ ‖(curlOperator (c+q) - curlOperator c - linearCurlOperator c q).adjoint‖ * ‖F‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖curlOperator (c+q) - curlOperator c - linearCurlOperator c q‖ * ‖F‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ (displacementSize q^2/2) * ν :=
      mul_le_mul (curlOperator_remainder c q) hF (norm_nonneg _) (by positivity)
    _ = _ := by ring

variable [CompleteSpace V]

/-- Compression of the actual shifted magnetic Fourier matrix. -/
def compression (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) : W →L[ℂ] V :=
  F.adjoint.comp ((Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (shiftedMagneticFourier material c t)).comp G)

/-- The exact first-order coefficient of the compressed curl sandwich. -/
def firstCompression (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c q : Momentum) (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) : W →L[ℂ] V :=
  sandwich (inverseMaterial material) (appliedLinear c q F) (appliedCurl c G) +
    sandwich (inverseMaterial material) (appliedCurl c F) (appliedLinear c q G)

private theorem map_shifted_sandwich
    {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [Ring B] [Algebra ℂ B] [StarRing B]
    (f : A ≃⋆ₐ[ℂ] B) (C D : A) (t : ℂ) :
    f (C * D * star C - t • 1) = f C * f D * star (f C) - t • 1 := by
  simp only [map_sub, map_mul, map_star, map_smul, map_one]

private theorem compression_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C D : H →L[ℂ] H) (t : ℂ) (F : V →L[ℂ] H) (G : W →L[ℂ] H) :
    F.adjoint.comp ((C * D * star C - t • 1).comp G) =
      sandwich D (C.adjoint.comp F) (C.adjoint.comp G) - t • F.adjoint.comp G := by
  simp only [sandwich, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_assoc]

theorem compression_sandwich (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) :
    compression material c t F G =
      sandwich (inverseMaterial material) (appliedCurl c F) (appliedCurl c G) -
        (t : ℂ) • F.adjoint.comp G := by
  have hm := map_shifted_sandwich (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ))
    (frequencyCurl c) (fourierInverseMass material) (t : ℂ)
  change Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (shiftedMagneticFourier material c t) =
    curlOperator c * inverseMaterial material * star (curlOperator c) - (t : ℂ) • 1 at hm
  unfold compression
  rw [hm]
  exact compression_identity (curlOperator c) (inverseMaterial material) (t : ℂ) F G

/-- The actual signed diagonal compression has remainder
`s²(ν e+ν²)`, with `e` the witnessed center-curl norm. -/
theorem diagonal_remainder_bound (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c q : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) (ν e : ℝ) (hν : 0 ≤ ν) (he : 0 ≤ e)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e) :
    ‖compression material (c+q) t F F - compression material c t F F -
        firstCompression material c q F F‖ ≤ displacementSize q^2 * (ν*e + ν^2) := by
  have hh := BoxCompression.diagonal_remainder_bound (inverseMaterial material)
    (appliedCurl c F) (appliedLinear c q F) (appliedIncrement c q F)
    (displacementSize q) ν e (displacementSize_nonneg q) hν he
    (inverseMaterial_norm material hm) hcenter (appliedIncrement_norm c q F ν hF)
    (appliedRemainder_norm c q F ν hF)
  have hid : compression material (c+q) t F F - compression material c t F F -
      firstCompression material c q F F =
      sandwich (inverseMaterial material) (appliedCurl c F + appliedIncrement c q F)
        (appliedCurl c F + appliedIncrement c q F) -
      sandwich (inverseMaterial material) (appliedCurl c F) (appliedCurl c F) -
      (sandwich (inverseMaterial material) (appliedLinear c q F) (appliedCurl c F) +
        sandwich (inverseMaterial material) (appliedCurl c F) (appliedLinear c q F)) := by
    rw [compression_sandwich, compression_sandwich, appliedCurl_add]
    unfold firstCompression
    module
  rw [hid]
  exact hh

/-- The actual mixed low/gradient compression has remainder
`νG s²(e/2+ν)` when the gradient witness lies in the center curl kernel. -/
theorem mixed_remainder_bound (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c q : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) (ν e νG : ℝ)
    (hν : 0 ≤ ν) (he : 0 ≤ e) (hνG : 0 ≤ νG)
    (hF : ‖F‖ ≤ ν) (hG : ‖G‖ ≤ νG) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hgradient : appliedCurl c G = 0) :
    ‖compression material (c+q) t F G - compression material c t F G -
        firstCompression material c q F G‖ ≤ νG * displacementSize q^2 * (e/2 + ν) := by
  have hh := BoxCompression.mixed_remainder_bound (inverseMaterial material)
    (appliedCurl c F) (appliedIncrement c q F) (appliedLinear c q G) (appliedIncrement c q G)
    (displacementSize q) ν e νG (displacementSize_nonneg q) hν he hνG
    (inverseMaterial_norm material hm) hcenter (appliedIncrement_norm c q F ν hF)
    (appliedIncrement_norm c q G νG hG) (appliedRemainder_norm c q G νG hG)
  have hid : compression material (c+q) t F G - compression material c t F G -
      firstCompression material c q F G =
      sandwich (inverseMaterial material) (appliedCurl c F + appliedIncrement c q F)
        (appliedIncrement c q G) -
      sandwich (inverseMaterial material) (appliedCurl c F) (appliedLinear c q G) := by
    rw [compression_sandwich, compression_sandwich, appliedCurl_add, appliedCurl_add]
    simp only [firstCompression, hgradient, zero_add, sandwich, ContinuousLinearMap.comp_zero,
      zero_add]
    module
  rw [hid]
  exact hh

end Maxwell.Spectral.BoxMagnetic
