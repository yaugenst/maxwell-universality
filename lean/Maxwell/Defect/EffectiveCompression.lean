import Maxwell.Defect.FiniteCompressionSpectral
import Maxwell.Defect.RealCompression
import Maxwell.Defect.WeightSearch
import Maxwell.Defect.ModeCertificate
import Maxwell.Defect.PhysicalCompression

/-! Exact finite-stencil matrices and executable rational weight searches
give effective enclosures of the actual infinite-volume compression. -/

namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice Filter Topology
variable {n : ℕ}

theorem compressionOperator_inverse_norm_le (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), δ ≤ |x|) :
    ‖compressionOperator edges (Ring.inverse (operator m K hK hm z))‖ ≤ δ⁻¹ := by
  let : IsometricContinuousFunctionalCalculus ℝ (Field →L[ℂ] Field) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  exact (compressionOperator_norm_le edges _).trans
    (inverse_norm_of_spectral_gap (operator m K hK hm z)
      (operator_selfAdjoint m K hK hm z) δ hδ hgap).2

noncomputable def realInverseCompression (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) :=
  realPartOperator (compressionOperator edges (Ring.inverse (operator m K hK hm z)))

noncomputable def weightedInverseCompression (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (W : Fin n → ℚ) :=
  sqrtWeightOperator W * realInverseCompression edges m K hK hm z * sqrtWeightOperator W

def effectiveCompressionMatrix (edges : Fin n ↪ Edge) (m : Edge → ℚ) (z M : ℚ)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  rationalWeightedMatrix (compression (coordinateBasis edges) m z ((M ^ 2)⁻¹) k)
    (sqrtWeightSearch W (1 / ((k : ℚ) + 1)) hW hW1 (by positivity))

def effectiveCompressionError (δ M : ℚ) (k : ℕ) : ℚ :=
  δ⁻¹ * (1 - δ ^ 2 / M ^ 2) ^ (k + 1) + 2 * δ⁻¹ / ((k : ℚ) + 1)

theorem effectiveCompressionMatrix_symmetric (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M : ℚ)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (k : ℕ) :
    (effectiveCompressionMatrix edges m z M W hW hW1 k).IsSymm := by
  apply rationalWeightedMatrix_isSymm
  exact compression_symmetric m K hK hm z _ k _

theorem effectiveCompressionError_nonneg (δ M : ℚ) (k : ℕ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    0 ≤ effectiveCompressionError δ M k := by
  have hratio : δ ^ 2 / M ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hM)).mpr (pow_le_pow_left₀ hδ.le hδM 2)
  unfold effectiveCompressionError
  positivity

/-- Every stage has a proved rational error bar relative to the actual
infinite inverse, including the irrational square-root source weights. -/
theorem effectiveCompressionMatrix_error (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ : ℚ)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (k : ℕ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) :
    ‖rationalOperator (effectiveCompressionMatrix edges m z M W hW hW1 k) -
      weightedInverseCompression edges m K hK hm z W‖ ≤
      (effectiveCompressionError δ M k : ℝ) := by
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hδMr : (δ : ℝ) ≤ M := by exact_mod_cast hδM
  let R := compressionOperator edges (Ring.inverse (operator m K hK hm z))
  let T := compression (coordinateBasis edges) m z ((M ^ 2)⁻¹) k
  have herror : ‖rationalOperator T - realPartOperator R‖ ≤
      (δ : ℝ)⁻¹ * (1 - (δ : ℝ) ^ 2 / (M : ℝ) ^ 2) ^ (k + 1) := by
    rw [norm_sub_rev]
    exact (realPartOperator_error R T).trans
      (rationalCompressionOperator_spectral_error edges m K hK hm z M δ k hδr hMr
        hδMr hnorm hgap)
  have hRn : ‖realPartOperator R‖ ≤ (δ : ℝ)⁻¹ :=
    (realPartOperator_norm_le R).trans
      (compressionOperator_inverse_norm_le edges m K hK hm z δ hδr hgap)
  have hweight := rational_weighted_compression_error W
    (sqrtWeightSearch W (1 / ((k : ℚ) + 1)) hW hW1 (by positivity))
    (1 / ((k : ℚ) + 1)) T (realPartOperator R)
    ((δ : ℝ)⁻¹ * (1 - (δ : ℝ) ^ 2 / (M : ℝ) ^ 2) ^ (k + 1)) (δ : ℝ)⁻¹
    hW hW1 (by positivity) (sqrtWeightSearch_spec W _ hW hW1 (by positivity)) herror hRn
  convert hweight using 1
  · rfl
  · simp only [effectiveCompressionError, Rat.cast_add, Rat.cast_mul, Rat.cast_inv,
      Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
    ring

theorem effectiveCompressionError_tendsto (δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    Tendsto (fun k => (effectiveCompressionError δ M k : ℝ)) atTop (𝓝 0) := by
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hδMr : (δ : ℝ) ≤ M := by exact_mod_cast hδM
  obtain ⟨hr0, hr1⟩ := inversePolynomial_factor_range hδr hMr hδMr
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
    (tendsto_add_atTop_nat 1)
  have h := (hp.const_mul (δ : ℝ)⁻¹).add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (δ : ℝ)⁻¹))
  convert h using 1
  · ext k
    simp only [effectiveCompressionError, Rat.cast_add, Rat.cast_mul, Rat.cast_inv,
      Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat,
      Function.comp_apply]
    ring
  · simp

theorem effectiveCompressionMatrix_tendsto (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ : ℚ)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) :
    Tendsto (fun k => rationalOperator (effectiveCompressionMatrix edges m z M W hW hW1 k))
      atTop (𝓝 (weightedInverseCompression edges m K hK hm z W)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (effectiveCompressionError_tendsto δ M hδ hM hδM)
  exact fun k => effectiveCompressionMatrix_error edges m K hK hm z M δ W hW hW1 k
    hδ hM hδM hnorm hgap

theorem unweightedCompression_tendsto (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) :
    Tendsto (fun k => complexRationalOperator
      (compression (coordinateBasis edges) m z ((M ^ 2)⁻¹) k)) atTop
      (𝓝 (compressionOperator edges (Ring.inverse (operator m K hK hm z)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (effectiveCompressionError_tendsto δ M hδ hM hδM)
  intro k
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hδMr : (δ : ℝ) ≤ M := by exact_mod_cast hδM
  rw [norm_sub_rev]
  apply (rationalCompressionOperator_spectral_error edges m K hK hm z M δ k hδr hMr
    hδMr hnorm hgap).trans
  simp only [effectiveCompressionError, Rat.cast_add, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
  exact le_add_of_nonneg_right (by positivity)

theorem weightedInverseCompression_realPart (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (W : Fin n → ℚ) :
    weightedInverseCompression edges m K hK hm z W =
      realPartOperator (sourceCompression (defectInjection edges W)
        (Ring.inverse (operator m K hK hm z))) := by
  rw [defectInjection_real_compression]
  rfl

theorem weightedInverseCompression_symmetric (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (W : Fin n → ℚ) :
    (weightedInverseCompression edges m K hK hm z W).toLinearMap.IsSymmetric := by
  rw [weightedInverseCompression_realPart]
  apply realPartOperator_symmetric
  exact sourceCompression_selfAdjoint _ _ (operator_selfAdjoint m K hK hm z).ringInverse

theorem weightedInverseCompression_norm_le (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (W : Fin n → ℚ)
    (hW1 : ∀ i, W i ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), δ ≤ |x|) :
    ‖weightedInverseCompression edges m K hK hm z W‖ ≤ δ⁻¹ := by
  have hD : ‖sqrtWeightOperator W‖ ≤ 1 := by
    apply weight_diagonal_norm_le _ 1 (by norm_num)
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by exact_mod_cast hW1 i)
  have hR : ‖realInverseCompression edges m K hK hm z‖ ≤ δ⁻¹ :=
    (realPartOperator_norm_le _).trans
      (compressionOperator_inverse_norm_le edges m K hK hm z δ hδ hgap)
  unfold weightedInverseCompression
  calc
    _ ≤ (‖sqrtWeightOperator W‖ * ‖realInverseCompression edges m K hK hm z‖) *
        ‖sqrtWeightOperator W‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * δ⁻¹) * 1 := by gcongr
    _ = _ := by ring

theorem weightedInverseCompression_eigenvalue_le (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (W : Fin n → ℚ)
    (hW1 : ∀ i, W i ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), δ ≤ |x|)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : ‖u‖ = 1)
    (heig : weightedInverseCompression edges m K hK hm z W u = μ • u) :
    μ ≤ δ⁻¹ := by
  have h := (weightedInverseCompression edges m K hK hm z W).le_opNorm u
  rw [heig, norm_smul, Real.norm_eq_abs, hu, mul_one, mul_one] at h
  exact (le_abs_self μ).trans (h.trans
    (weightedInverseCompression_norm_le edges m K hK hm z W hW1 δ hδ hgap))

/-- The true complex compressed eigenspace is one-dimensional whenever
the finite rational checker certifies the real restriction as simple. -/
theorem weightedInverseCompression_simple_complex (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ : ℚ)
    (W : Fin n → ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : u ≠ 0)
    (heig : weightedInverseCompression edges m K hK hm z W u = μ • u)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace
      (weightedInverseCompression edges m K hK hm z W).toLinearMap μ) = 1) :
    let S := sourceCompression (defectInjection edges W) (Ring.inverse (operator m K hK hm z))
    S (realCoordinateEmbedding u) = (μ : ℂ) • realCoordinateEmbedding u ∧
      Module.finrank ℂ (Module.End.eigenspace S.toLinearMap (μ : ℂ)) = 1 := by
  dsimp only
  let R := compressionOperator edges (Ring.inverse (operator m K hK hm z))
  let S := sourceCompression (defectInjection edges W) (Ring.inverse (operator m K hK hm z))
  have hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator S x) = S (realCoordinateEmbedding x) := by
    intro x
    have hSC : S = complexSqrtWeightOperator W * R * complexSqrtWeightOperator W :=
      defectInjection_compression edges W _
    rw [hSC]
    apply weighted_real_coordinates
    exact realPartOperator_intertwine_of_limit _ R
      (unweightedCompression_tendsto edges m K hK hm z M δ hδ hM hδM hnorm hgap)
  have hS : weightedInverseCompression edges m K hK hm z W = realPartOperator S :=
    weightedInverseCompression_realPart edges m K hK hm z W
  rw [hS] at heig hsimple
  constructor
  · change S (realCoordinateEmbedding u) = _
    rw [← hreal, heig, map_smul]
    ext i
    simp
  · exact realPartOperator_simple_complex S hreal u μ hu heig hsimple

/-- At a true simple mode, the concrete finite-stencil checker terminates.
The only source data are rational enclosures; all operator approximations
and error bars are the executable constructions above. -/
theorem effectiveCompression_mode_search_terminates
    (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ : ℚ)
    (W : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|)
    (u w : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (threshold : ℚ)
    (q : ℕ → Fin n → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hu : ‖u‖ = 1)
    (hSu : weightedInverseCompression edges m K hK hm z W u = μ • u)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace
      (weightedInverseCompression edges m K hK hm z W).toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (hsourceBound : 0 < sourceBound) :
    ∃ stage : ℕ,
      modeCertificateCheck
        (effectiveCompressionMatrix edges m z M W hW hW1 (Nat.unpair stage).1)
        (effectiveCompressionError δ M (Nat.unpair stage).1) threshold
        (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) sourceBound
        (Nat.unpair stage).2 = true := by
  exact modeCertificate_search_terminates
    (weightedInverseCompression edges m K hK hm z W) u w μ
    (effectiveCompressionMatrix edges m z M W hW hW1) (effectiveCompressionError δ M)
    threshold q β sourceBound hu hSu hsimple hthreshold hoverlap
    (effectiveCompressionMatrix_symmetric edges m K hK hm z M W hW hW1)
    (fun k => effectiveCompressionError_nonneg δ M k hδ hM hδM)
    (effectiveCompressionMatrix_tendsto edges m K hK hm z M δ W hW hW1
      hδ hM hδM hnorm hgap)
    (effectiveCompressionError_tendsto δ M hδ hM hδM) hq hβlim hw hsourceBound

end Maxwell.Defect.FiniteStencil
