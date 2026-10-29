import Maxwell.Defect.SimpleCertificate
import Maxwell.Defect.EdgeSourceEnclosure
import Maxwell.Defect.RankOneSpectral

/-! Quantitative polynomial-filter inputs derived from an accepted finite
simple-mode certificate. The selected eigenspace is the one certified by
that same certificate, with an explicit rational initial projection bound. -/

namespace Maxwell.Defect

open InnerProductSpace Module.End

variable {n : ℕ}

/-- A rational positive lower bound for half the norm of a nonzero
rational vector, requiring no square-root operation. -/
def filterProjectionLower (v : Fin n → ℚ) : ℚ :=
  rationalNormSq v / (2 * EdgeSourceEnclosure.referenceBound v)

theorem filterProjectionLower_pos (v : Fin n → ℚ) (hv : v ≠ 0) :
    0 < filterProjectionLower v := by
  have hn : 0 < ‖rationalVector v‖ := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have hq : 0 < rationalNormSq v := by
    have hh : (0 : ℝ) < (rationalNormSq v : ℝ) := by rw [rationalNormSq_cast]; positivity
    exact_mod_cast hh
  exact div_pos hq (mul_pos (by norm_num) (EdgeSourceEnclosure.referenceBound_pos v))

theorem filterProjectionLower_le_half_norm (v : Fin n → ℚ) :
    (filterProjectionLower v : ℝ) ≤ ‖rationalVector v‖ / 2 := by
  have hM : (0 : ℝ) < EdgeSourceEnclosure.referenceBound v := by
    exact_mod_cast EdgeSourceEnclosure.referenceBound_pos v
  have hnorm := EdgeSourceEnclosure.reference_norm_le v
  simp only [filterProjectionLower, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, rationalNormSq_cast]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * EdgeSourceEnclosure.referenceBound v by positivity)).mpr
  nlinarith [mul_nonneg (norm_nonneg (rationalVector v)) (sub_nonneg.mpr hnorm)]

/-- A positive certified overlap with the actual selected unit eigenvector
forces the same quantitative component in its orthogonal eigenspace projection. -/
theorem selectedProjection_norm_lower_of_overlap
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℚ)
    (hu : ‖u‖ = 1) (heig : S u = μ • u) (hv : v ≠ 0)
    (hoverlap : (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector v) u) :
    ‖rationalVector v‖ / 2 ≤ ‖selectedProjection S μ (rationalVector v)‖ := by
  have hn : 0 < ‖rationalVector v‖ := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have hscale : ‖rationalVector v‖ • rationalUnitVector v = rationalVector v := by
    simp [rationalUnitVector, smul_smul, hn.ne']
  have hi : inner ℝ (rationalVector v) u =
      ‖rationalVector v‖ * inner ℝ (rationalUnitVector v) u := by
    conv_lhs => rw [← hscale]
    simp only [inner_smul_left, conj_trivial]
  have ho := (eigenspace S.toLinearMap μ).starProjection_inner_eq_zero
    (rationalVector v) u (mem_eigenspace_iff.mpr heig)
  have hp : inner ℝ (rationalVector v) u =
      inner ℝ (selectedProjection S μ (rationalVector v)) u := by
    simpa only [inner_sub_left, sub_eq_zero, selectedProjection] using ho
  have hb : inner ℝ (rationalVector v) u ≤ ‖selectedProjection S μ (rationalVector v)‖ := by
    rw [hp]
    exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans_eq (by rw [hu, mul_one]))
  rw [hi] at hb
  nlinarith

private theorem unit_eigenvector_of_spectrum
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : ℝ) (hρ : ρ ∈ spectrum ℝ S) :
    ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧ S y = ρ • y := by
  rw [ContinuousLinearMap.spectrum_eq] at hρ
  obtain ⟨v, hv⟩ := (HasEigenvalue.of_mem_spectrum hρ).exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, norm_ne_zero_iff.mpr hv0]
  · have he : S v = ρ • v := hv.apply_eq_smul
    rw [map_smul, he]
    exact smul_comm _ _ _

theorem exists_rational_filter_bound
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (target gap : ℚ) :
    ∃ M : ℚ, 0 < M ∧ gap ≤ M ∧ ‖S‖ + |(target : ℝ)| ≤ (M : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (‖S‖ + |(target : ℝ)|) (gap : ℝ))
  have hn := (le_max_left (‖S‖ + |(target : ℝ)|) (gap : ℝ)).trans_lt hM
  have hg := (le_max_right (‖S‖ + |(target : ℝ)|) (gap : ℝ)).trans_lt hM
  refine ⟨M, ?_, by exact_mod_cast hg.le, by exact_mod_cast hn.le⟩
  exact_mod_cast (show (0 : ℝ) < M by linarith [norm_nonneg S, abs_nonneg (target : ℝ)])

/-- Tightened finite residual checks yield all filter parameters for the
same actual eigenvalue returned by certificate soundness. In particular,
the initial selected projection has a proved positive rational lower bound. -/
theorem SimpleCertificate.filter_data_with_sound (c : SimpleCertificate n)
    (T : Matrix (Fin n) (Fin n) ℚ) (error : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hcheck : c.accepts T error = true)
    (htight : 8 * (error + 2 * c.residual) < c.gap) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin n),
      |μ - (c.target : ℝ)| ≤ (error : ℝ) + 2 * (c.residual : ℝ) ∧
      ‖u - rationalUnitVector c.vector‖ ≤
        4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ) ∧
      ‖u‖ = 1 ∧ S u = μ • u ∧
      Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1 ∧
      |μ - (c.target : ℝ)| ≤ (c.gap : ℝ) / 4 ∧
      (∀ ρ ∈ spectrum ℝ S, ρ ≠ μ → (c.gap : ℝ) / 2 ≤ |ρ - (c.target : ℝ)|) ∧
      (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector c.vector) u ∧
      ‖u - rationalUnitVector c.vector‖ < 1 / 2 ∧
      ‖rationalVector c.vector‖ / 2 ≤ ‖selectedProjection S μ (rationalVector c.vector)‖ ∧
      0 < filterProjectionLower c.vector ∧
      (filterProjectionLower c.vector : ℝ) ≤ ‖selectedProjection S μ (rationalVector c.vector)‖ ∧
      selectedProjection S μ (rationalVector c.vector) ≠ 0 ∧
      ∃ M : ℚ, 0 < M ∧ c.gap ≤ M ∧ ‖S‖ + |(c.target : ℝ)| ≤ (M : ℝ) := by
  obtain ⟨_, hv, he, hr, _, _, _⟩ := of_decide_eq_true hcheck
  have he' : (0 : ℝ) ≤ error := by exact_mod_cast he
  have hr' : (0 : ℝ) < c.residual := by exact_mod_cast hr
  have htight' : 8 * ((error : ℝ) + 2 * (c.residual : ℝ)) < (c.gap : ℝ) := by exact_mod_cast htight
  have hg : (0 : ℝ) < c.gap := by linarith
  obtain ⟨μ, u, hu, heig, htarget, hsimple, _, hdir, hother⟩ := c.sound T error S hS happrox hcheck
  have hd : ‖u - rationalUnitVector c.vector‖ < 1 / 2 :=
    hdir.trans_lt ((div_lt_iff₀ hg).mpr (by linarith))
  have hvnorm : ‖rationalUnitVector c.vector‖ = 1 := rationalUnitVector_norm _ hv
  have hi : (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector c.vector) u := by
    have hh := abs_real_inner_le_norm (rationalUnitVector c.vector) (rationalUnitVector c.vector - u)
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hvnorm, one_pow, one_mul, norm_sub_rev] at hh
    have hle := (le_abs_self (1 - inner ℝ (rationalUnitVector c.vector) u)).trans hh
    linarith
  have hp := selectedProjection_norm_lower_of_overlap S μ u c.vector hu heig hv hi
  have hp0 := filterProjectionLower_pos c.vector hv
  have hpbound := (filterProjectionLower_le_half_norm c.vector).trans hp
  have hpne : selectedProjection S μ (rationalVector c.vector) ≠ 0 := by
    apply norm_pos_iff.mp
    exact (show (0 : ℝ) < filterProjectionLower c.vector by exact_mod_cast hp0).trans_le hpbound
  refine ⟨μ, u, htarget, hdir, hu, heig, hsimple, ?_, ?_, hi, hd, hp, hp0, hpbound, hpne,
    exists_rational_filter_bound S c.target c.gap⟩
  · linarith
  · intro ρ hρ hne
    obtain ⟨y, hy, heigy⟩ := unit_eigenvector_of_spectrum S ρ hρ
    have hsep := hother ρ y hy heigy hne.symm
    have htriangle : |ρ - μ| ≤ |ρ - (c.target : ℝ)| + |μ - (c.target : ℝ)| := by
      simpa only [abs_sub_comm (c.target : ℝ) μ] using abs_sub_le ρ (c.target : ℝ) μ
    linarith

/-- Quantitative filter data, retaining the original API. The stronger
`filter_data_with_sound` also preserves the certificate's sharp residual bounds. -/
theorem SimpleCertificate.filter_data (c : SimpleCertificate n)
    (T : Matrix (Fin n) (Fin n) ℚ) (error : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hcheck : c.accepts T error = true)
    (htight : 8 * (error + 2 * c.residual) < c.gap) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧ S u = μ • u ∧
      Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1 ∧
      |μ - (c.target : ℝ)| ≤ (c.gap : ℝ) / 4 ∧
      (∀ ρ ∈ spectrum ℝ S, ρ ≠ μ → (c.gap : ℝ) / 2 ≤ |ρ - (c.target : ℝ)|) ∧
      (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector c.vector) u ∧
      ‖u - rationalUnitVector c.vector‖ < 1 / 2 ∧
      ‖rationalVector c.vector‖ / 2 ≤ ‖selectedProjection S μ (rationalVector c.vector)‖ ∧
      0 < filterProjectionLower c.vector ∧
      (filterProjectionLower c.vector : ℝ) ≤ ‖selectedProjection S μ (rationalVector c.vector)‖ ∧
      selectedProjection S μ (rationalVector c.vector) ≠ 0 ∧
      ∃ M : ℚ, 0 < M ∧ c.gap ≤ M ∧ ‖S‖ + |(c.target : ℝ)| ≤ (M : ℝ) := by
  obtain ⟨μ, u, _, _, hdata⟩ :=
    c.filter_data_with_sound T error S hS happrox hcheck htight
  exact ⟨μ, u, hdata⟩

end Maxwell.Defect
