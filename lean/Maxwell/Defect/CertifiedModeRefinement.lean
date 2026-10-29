import Maxwell.Defect.ModeRefinement
import Maxwell.Defect.CertifiedFilterData
import Maxwell.Defect.SelectedModeOrientation
import Maxwell.Defect.ModeBudgetCertificate

/-! The selected mode is refined using rational data obtained from the same
finite certificate that certifies the mode and its source overlap. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End
variable {n : ℕ}

def filterRatio (gap bound : ℚ) : ℚ := filterUpper gap bound / filterLower gap bound

theorem filterRatio_range (gap bound : ℚ) (hg : 0 < gap) (hM : 0 < bound)
    (hgM : gap ≤ bound) : 0 ≤ filterRatio gap bound ∧ filterRatio gap bound < 1 := by
  have h := filter_parameter_range gap bound hg hM hgM
  have hl : 0 < filterLower gap bound := lt_of_lt_of_le (by norm_num) h.2.2.1
  exact ⟨div_nonneg h.1 hl.le, (div_lt_one hl).mpr h.2.1⟩

def certifiedModeApproximation
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C target gap M B p : ℚ)
    (hg : 0 < gap) (hM : 0 < M) (hgM : gap ≤ M) (hB : 0 < B) (hp : 0 < p)
    (v : Fin n → ℚ) (b : ℕ) : Fin n → ℚ :=
  rationalModeApproximation T C target M B p (filterRatio gap M) hB hp
    (filterRatio_range gap M hg hM hgM).1 (filterRatio_range gap M hg hM hgM).2 v b

set_option maxHeartbeats 800000 in
theorem certifiedModeApproximation_spec
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C target gap M B p : ℚ)
    (hg : 0 < gap) (hM : 0 < M) (hgM : gap ≤ M) (hC : 0 ≤ C)
    (hB : 0 < B) (hp : 0 < p) (μ : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (heig : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hμ : |μ - (target : ℝ)| ≤ (gap : ℝ) / 4)
    (hother : ∀ σ ∈ spectrum ℝ S, σ ≠ μ → (gap : ℝ) / 2 ≤ |σ - (target : ℝ)|)
    (hnorm : ‖S‖ + |(target : ℝ)| ≤ (M : ℝ))
    (herr : ∀ b, ‖S - rationalOperator (T b)‖ ≤ (C : ℝ) * (1 / 2 : ℝ)^b)
    (v : Fin n → ℚ) (hv0 : v ≠ 0) (hv : ‖rationalVector v‖ ≤ (B : ℝ))
    (hoverlap : (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector v) u)
    (hproj : (p : ℝ) ≤ ‖selectedProjection S μ (rationalVector v)‖) (b : ℕ) :
    ‖rationalVector (certifiedModeApproximation T C target gap M B p hg hM hgM hB hp v b)‖ ≤ 1 ∧
    ‖rationalVector (certifiedModeApproximation T C target gap M B p hg hM hgM hB hp v b) - u‖ ≤
      (1 / 2 : ℝ)^b := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hgr : (0 : ℝ) < gap := by exact_mod_cast hg
  have hrange := filter_parameter_range gap M hg hM hgM
  have hlo : (1 / 2 : ℝ) ≤ (filterLower gap M : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hrange.2.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have hβ : (0 : ℝ) ≤ (filterUpper gap M : ℝ) := by exact_mod_cast hrange.1
  have hselected : (filterLower gap M : ℝ) ≤ scalarModeFilter target ((M : ℝ)^2)⁻¹ μ := by
    simpa only [filterLower, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_mul, Rat.cast_ofNat] using scalarModeFilter_selected target M gap μ hMr hgr.le hμ
  have hρ := filterRatio_range gap M hg hM hgM
  have hβα : (filterUpper gap M : ℝ) ≤
      (filterRatio gap M : ℝ) * scalarModeFilter target ((M : ℝ)^2)⁻¹ μ := by
    have hr : (0 : ℝ) ≤ (filterRatio gap M : ℝ) := by exact_mod_cast hρ.1
    have hh := mul_le_mul_of_nonneg_left hselected hr
    have hcancel : (filterRatio gap M : ℝ) * (filterLower gap M : ℝ) =
        (filterUpper gap M : ℝ) := by
      simp only [filterRatio, Rat.cast_div]
      exact div_mul_cancel₀ _ (ne_of_gt (lt_of_lt_of_le (by norm_num) hlo))
    rwa [hcancel] at hh
  have hfilter : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target ((M : ℝ)^2)⁻¹ (hS.eigenvalues rfl i)| ≤ (filterUpper gap M : ℝ) := by
    intro i hi
    have hdist : |hS.eigenvalues rfl i - (target : ℝ)| ≤ (M : ℝ) :=
      (abs_sub _ _).trans ((add_le_add (eigenvalue_abs_le_norm S hS i)
        (le_refl |(target : ℝ)|)).trans hnorm)
    have hmem : hS.eigenvalues rfl i ∈ spectrum ℝ S := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact (hS.hasEigenvalue_eigenvalues rfl i).mem_spectrum
    simpa only [filterUpper, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_mul, Rat.cast_ofNat] using scalarModeFilter_complement target M gap
        (hS.eigenvalues rfl i) hMr hgr.le hdist (hother _ hmem hi)
  have hh := rationalModeApproximation_spec S hS T C target M B p (filterRatio gap M)
    hM hC hB hp hρ.1 hρ.2 μ (filterUpper gap M) hβ (hlo.trans hselected) hβα
    hfilter hnorm herr v hv hproj b
  rw [normalize_selectedProjection_of_rational_overlap S μ u v hu heig hsimple hv0 hoverlap] at hh
  exact hh

/-- All numerical inputs used after the finite startup search. -/
structure ModeRefinementPlan (n : ℕ) where
  target : ℚ
  gap : ℚ
  bound : ℚ
  normBound : ℚ
  projectionLower : ℚ
  initial : Fin n → ℚ
  gap_pos : 0 < gap
  bound_pos : 0 < bound
  gap_le_bound : gap ≤ bound
  normBound_pos : 0 < normBound
  projectionLower_pos : 0 < projectionLower

def ModeRefinementPlan.approximation (P : ModeRefinementPlan n)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C : ℚ) (b : ℕ) : Fin n → ℚ :=
  certifiedModeApproximation T C P.target P.gap P.bound P.normBound P.projectionLower
    P.gap_pos P.bound_pos P.gap_le_bound P.normBound_pos P.projectionLower_pos P.initial b

set_option maxHeartbeats 800000 in
theorem modeBudget_refinement (c : SimpleCertificate n) (a : ℚ)
    (T : Matrix (Fin n) (Fin n) ℚ) (error threshold : ℚ)
    (q : Fin n → ℚ) (β M budget : ℚ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ (error : ℝ))
    (hq : ‖w - rationalVector q‖ ≤ (β : ℝ)) (hw : ‖w‖ ≤ (M : ℝ))
    (hcheck : modeBudgetAccepts c a T error threshold q β M budget = true)
    (binary : ℕ → Matrix (Fin n) (Fin n) ℚ) (C : ℚ) (hC : 0 ≤ C)
    (hbinary : ∀ b, ‖S - rationalOperator (binary b)‖ ≤ (C : ℝ) * (1 / 2 : ℝ)^b) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧ S u = μ • u ∧
      (threshold : ℝ) < μ ∧ Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1 ∧
      (budget : ℝ) < |inner ℝ w u| ^ 2 ∧
      ∃ P : ModeRefinementPlan n, ∀ b,
        ‖rationalVector (P.approximation binary C b)‖ ≤ 1 ∧
        ‖rationalVector (P.approximation binary C b) - u‖ ≤ (1 / 2 : ℝ)^b := by
  obtain ⟨hc, hb⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hbudget, hbmargin, htight⟩ := of_decide_eq_true hb
  obtain ⟨hcert, _, _, ha, hthreshold, hoverlap, hmargin⟩ := of_decide_eq_true hc
  obtain ⟨μ, u, htarget, hdir, hu, heig, hsimple, htargetQuarter, hother, horient,
    _, _, hp, hproj, _, bound, hbound, hgapbound, hnorm⟩ :=
    c.filter_data_with_sound T error S hS happrox hcert htight
  have hv : c.vector ≠ 0 := (of_decide_eq_true hcert).2.1
  have he : 0 ≤ error := (of_decide_eq_true hcert).2.2.1
  have hr : 0 < c.residual := (of_decide_eq_true hcert).2.2.2.1
  have hg : 0 < c.gap := by linarith
  have hlow := (rationalOverlap_lower_iff q c.vector a hv ha.le).mp hoverlap
  have hthr : (threshold : ℝ) < (c.target : ℝ) -
      ((error : ℝ) + 2 * (c.residual : ℝ)) := by exact_mod_cast hthreshold
  have hpos : 0 < (a : ℝ) - (β : ℝ) - (M : ℝ) *
      (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) := by
    have hh : (β : ℝ) + (M : ℝ) *
        (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) < a := by
      exact_mod_cast hmargin
    linarith
  have hsource := source_overlap_enclosure w (rationalVector q) (rationalUnitVector c.vector) u
    β M (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ))
    (rationalUnitVector_norm _ hv) hq hw hdir
  have hbudget' : (budget : ℝ) < ((certifiedOverlapLower c a error β M : ℚ) : ℝ)^2 := by
    exact_mod_cast hbmargin
  simp only [certifiedOverlapLower, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_add, Rat.cast_ofNat] at hbudget'
  have hsourceLower : (a : ℝ) - (β : ℝ) - (M : ℝ) *
      (4 * ((error : ℝ) + 2 * (c.residual : ℝ)) / (c.gap : ℝ)) ≤ |inner ℝ w u| := by
    linarith
  let P : ModeRefinementPlan n := ⟨c.target, c.gap, bound,
    EdgeSourceEnclosure.referenceBound c.vector, filterProjectionLower c.vector, c.vector,
    hg, hbound, hgapbound, EdgeSourceEnclosure.referenceBound_pos c.vector, hp⟩
  refine ⟨μ, u, hu, heig, ?_, hsimple,
    hbudget'.trans_le (pow_le_pow_left₀ hpos.le hsourceLower 2), P, ?_⟩
  · linarith [(abs_le.mp htarget).1]
  · intro b
    exact certifiedModeApproximation_spec S hS binary C c.target c.gap bound
      (EdgeSourceEnclosure.referenceBound c.vector) (filterProjectionLower c.vector)
      hg hbound hgapbound hC (EdgeSourceEnclosure.referenceBound_pos c.vector) hp μ u
      hu heig hsimple htargetQuarter hother hnorm hbinary c.vector hv
      (EdgeSourceEnclosure.reference_norm_le c.vector) horient hproj b

end Maxwell.Defect
