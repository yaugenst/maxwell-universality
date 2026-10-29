import Maxwell.Defect.RankOneSpectral
import Maxwell.Defect.IntegralChart
import Maxwell.Defect.Coherence
import Maxwell.Defect.Search

/-! Composition of the coherent-source Rayleigh estimate, actual integral
sqrt expansion, and branch theorem. The resulting simple mode is a
conclusion; it is not included among the search hypotheses. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual spectral decomposition selects a high eigenspace with a
nonzero source projection, even if that eigenspace is degenerate. -/
theorem rayleigh_selects_nonzero_projection
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (w : E) (threshold : ℝ)
    (hRayleigh : threshold * ‖w‖ ^ 2 < inner ℝ w (A w)) :
    ∃ lam : ℝ, threshold < lam ∧ selectedProjection A lam w ≠ 0 := by
  classical
  let b := hA.eigenvectorBasis rfl
  let d := hA.eigenvalues rfl
  have hnorm : ∑ i, (b.repr w i) ^ 2 = ‖w‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    simp
  have hinner : inner ℝ w (A w) = ∑ i, d i * (b.repr w i) ^ 2 := by
    rw [← b.repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [show b.repr (A w) i = d i * b.repr w i from
      hA.eigenvectorBasis_apply_self_apply rfl w i]
    simp only [star_trivial]
    ring
  obtain ⟨i, hi, hwi⟩ := spectral_weight_above_threshold d (fun i => (b.repr w i) ^ 2)
    threshold (fun _ => sq_nonneg _) (by simpa only [hnorm, ← hinner] using hRayleigh)
  refine ⟨d i, hi, ?_⟩
  intro hz
  have hcoords := spectral_coordinates_projection A hA (d i) w
  rw [hz, map_zero] at hcoords
  have hi0 := congrArg (fun x => x i) hcoords
  simp only [PiLp.zero_apply, spectralP_apply, d] at hi0
  change 0 = b.repr w i at hi0
  exact hwi (by rw [← hi0]; norm_num)

/-- The actual rank-one branch retains any strict eigenvalue threshold and
any fixed linear numerator budget on a whole positive interval. -/
theorem rankOne_branch_strict_margins
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (S : ℝ → E →L[ℝ] E) (w : E) (lam c C r threshold numeratorBudget : ℝ)
    (ha : selectedProjection A lam w ≠ 0) (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r)
    (hthreshold : threshold < lam)
    (hS : ∀ τ, (S τ).toLinearMap.IsSymmetric)
    (hrem : ∀ τ, 0 < τ → τ < r →
      ‖S τ - A + (c * τ) • rankOne ℝ w w‖ ≤ C * τ ^ 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ, 0 < τ → τ < η →
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ S τ u = ν • u ∧ threshold < ν ∧
        Module.finrank ℝ (eigenspace (S τ).toLinearMap ν) = 1 ∧
        0 < inner ℝ w u ∧ numeratorBudget * τ < |inner ℝ w u| ^ 2 := by
  let a := selectedProjection A lam w
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨η, K, L, hη, hK, hL, hbranch⟩ := rankOne_branch_selection A hA S w lam c C r
    ha hc hC hr hS hrem
  let coefficient : Fin 4 → ℝ := ![1, c * ‖a‖ ^ 2 + K, ‖w‖ * L, numeratorBudget]
  let target : Fin 4 → ℝ := ![1, lam - threshold, ‖a‖ / 2, ‖a‖ ^ 2 / 4]
  have htarget : ∀ i, 0 < target i := by
    intro i
    fin_cases i <;> dsimp [target]
    · norm_num
    · linarith
    · positivity
    · positivity
  obtain ⟨η', hη', hsmall⟩ := exists_small_positive_linear coefficient target htarget
  refine ⟨min η η', lt_min hη hη', ?_⟩
  intro τ hτ hτη
  obtain ⟨ν, u, hu, hSu, hν, hdim, _, hover, hpos, _⟩ :=
    hbranch τ hτ (lt_of_lt_of_le hτη (min_le_left _ _))
  have hs := hsmall τ hτ (lt_of_lt_of_le hτη (min_le_right _ _))
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  simp only [coefficient, target, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, one_mul] at h0 h1 h2 h3
  have hKsq : K * τ ^ 2 ≤ K * τ := by
    have hτsq : τ ^ 2 ≤ τ := by nlinarith
    exact mul_le_mul_of_nonneg_left hτsq hK
  have hνlower := (abs_le.mp hν).1
  have hoverlower := (abs_le.mp hover).1
  change -(K * τ ^ 2) ≤ ν - (lam - c * ‖a‖ ^ 2 * τ) at hνlower
  have hlower : threshold < ν := by nlinarith
  have hinner : ‖a‖ / 2 < inner ℝ w u := by
    change - (‖w‖ * L * τ) ≤ inner ℝ w u - ‖a‖ at hoverlower
    linarith
  refine ⟨ν, u, hu, hSu, hlower, hdim, hpos, ?_⟩
  rw [sq_abs]
  nlinarith

/-- A proved square-root expansion of the actual compression yields
simple modes with all strict margins on a whole interval below the edge. -/
theorem sqrt_expansion_simple_modes
    (S : ℝ → E →L[ℝ] E) (w : E) (c C r threshold numeratorBudget : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r)
    (hS : ∀ ξ, (S ξ).toLinearMap.IsSymmetric)
    (hRayleigh : threshold * ‖w‖ ^ 2 < inner ℝ w (S 0 w))
    (hexp : ∀ ξ, 0 < ξ → ξ ≤ r →
      ‖S 0 - S ξ - (c * Real.sqrt ξ) • rankOne ℝ w w‖ ≤ C * ξ) :
    ∃ ξmax : ℝ, 0 < ξmax ∧ ∀ ξ, 0 < ξ → ξ < ξmax →
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ S ξ u = ν • u ∧ threshold < ν ∧
        Module.finrank ℝ (eigenspace (S ξ).toLinearMap ν) = 1 ∧
        0 < inner ℝ w u ∧ numeratorBudget * Real.sqrt ξ < |inner ℝ w u| ^ 2 := by
  obtain ⟨lam, hlam, ha⟩ := rayleigh_selects_nonzero_projection
    (S 0) (hS 0) w threshold hRayleigh
  have hroot : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hrem : ∀ τ, 0 < τ → τ < Real.sqrt r →
      ‖S (τ ^ 2) - S 0 + (c * τ) • rankOne ℝ w w‖ ≤ C * τ ^ 2 := by
    intro τ hτ hτr
    have hτsq : τ ^ 2 ≤ r := by nlinarith [Real.sq_sqrt hr.le]
    have hh := hexp (τ ^ 2) (sq_pos_of_pos hτ) hτsq
    rw [Real.sqrt_sq hτ.le] at hh
    have hid : S (τ ^ 2) - S 0 + (c * τ) • rankOne ℝ w w =
      -(S 0 - S (τ ^ 2) - (c * τ) • rankOne ℝ w w) := by abel
    simpa only [hid, norm_neg] using hh
  obtain ⟨η, hη, hbranch⟩ := rankOne_branch_strict_margins (S 0) (hS 0)
    (fun τ => S (τ ^ 2)) w lam c C (Real.sqrt r) threshold numeratorBudget
    ha hc hC hroot hlam (fun τ => hS (τ ^ 2)) hrem
  refine ⟨η ^ 2, sq_pos_of_pos hη, ?_⟩
  intro ξ hξ hξmax
  have hsqrt : Real.sqrt ξ < η := (Real.sqrt_lt hξ.le hη.le).mpr hξmax
  obtain ⟨ν, u, hu, hSu, hν, hdim, hpos, hnum⟩ := hbranch (Real.sqrt ξ)
    (Real.sqrt_pos.mpr hξ) hsqrt
  rw [Real.sq_sqrt hξ.le] at hSu hdim
  exact ⟨ν, u, hu, hSu, hν, hdim, hpos, hnum⟩

/-- The interval supplied by an actual square-root expansion contains a
positive dyadic energy, including when the edge itself is irrational. -/
theorem sqrt_expansion_dyadic_simple_mode
    (S : ℝ → E →L[ℝ] E) (w : E) (c C r edge threshold numeratorBudget : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r) (hedge : 0 < edge)
    (hS : ∀ ξ, (S ξ).toLinearMap.IsSymmetric)
    (hRayleigh : threshold * ‖w‖ ^ 2 < inner ℝ w (S 0 w))
    (hexp : ∀ ξ, 0 < ξ → ξ ≤ r →
      ‖S 0 - S ξ - (c * Real.sqrt ξ) • rankOne ℝ w w‖ ≤ C * ξ) :
    ∃ index : ℕ, 0 < (dyadicCandidate index : ℝ) ∧ (dyadicCandidate index : ℝ) < edge ∧
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ S (edge - (dyadicCandidate index : ℝ)) u = ν • u ∧
        threshold < ν ∧
        Module.finrank ℝ (eigenspace (S (edge - (dyadicCandidate index : ℝ))).toLinearMap ν) = 1 ∧
        0 < inner ℝ w u ∧
        numeratorBudget * Real.sqrt (edge - (dyadicCandidate index : ℝ)) < |inner ℝ w u| ^ 2 := by
  obtain ⟨ξmax, hξmax, hmode⟩ := sqrt_expansion_simple_modes S w c C r threshold numeratorBudget
    hc hC hr hS hRayleigh hexp
  obtain ⟨index, hi0, hie, hξ⟩ := exists_positive_dyadic_candidate hedge hξmax
  exact ⟨index, hi0, hie, hmode _ (sub_pos.mpr hie) hξ⟩

/-- Integral-chart hypotheses yield actual simple compressed modes on an
entire interval below the edge, with threshold and numerator margins. -/
theorem integralChart_simple_modes {X : Type*} [MeasurableSpace X] {measure : MeasureTheory.Measure X}
    (chart : IntegralChart (E →L[ℝ] E) X measure) (w : E) (threshold numeratorBudget : ℝ)
    (hW : chart.edgeNumerator = rankOne ℝ w w)
    (hS : ∀ ξ, (chart.compression ξ).toLinearMap.IsSymmetric)
    (hRayleigh : threshold * ‖w‖ ^ 2 < inner ℝ w (chart.compression 0 w)) :
    ∃ ξmax : ℝ, 0 < ξmax ∧ ∀ ξ, 0 < ξ → ξ < ξmax →
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ chart.compression ξ u = ν • u ∧ threshold < ν ∧
        Module.finrank ℝ (eigenspace (chart.compression ξ).toLinearMap ν) = 1 ∧
        0 < inner ℝ w u ∧ numeratorBudget * Real.sqrt ξ < |inner ℝ w u| ^ 2 := by
  apply sqrt_expansion_simple_modes chart.compression w chart.edgeCoefficient
    chart.remainderConstant (chart.gap / 2) threshold numeratorBudget
    chart.edgeCoefficient_pos chart.remainderConstant_nonneg (half_pos chart.gap_pos) hS hRayleigh
  intro ξ hξ hsmall
  simpa only [hW] using chart.sqrt_expansion hξ hsmall

/-- The actual simple-mode interval contains a positive dyadic operating
shift even when the background edge is irrational. -/
theorem integralChart_dyadic_simple_mode {X : Type*} [MeasurableSpace X]
    {measure : MeasureTheory.Measure X}
    (chart : IntegralChart (E →L[ℝ] E) X measure) (w : E)
    (edge threshold numeratorBudget : ℝ) (hedge : 0 < edge)
    (hW : chart.edgeNumerator = rankOne ℝ w w)
    (hS : ∀ ξ, (chart.compression ξ).toLinearMap.IsSymmetric)
    (hRayleigh : threshold * ‖w‖ ^ 2 < inner ℝ w (chart.compression 0 w)) :
    ∃ index : ℕ, 0 < (dyadicCandidate index : ℝ) ∧ (dyadicCandidate index : ℝ) < edge ∧
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧
        chart.compression (edge - (dyadicCandidate index : ℝ)) u = ν • u ∧
        threshold < ν ∧
        Module.finrank ℝ (eigenspace
          (chart.compression (edge - (dyadicCandidate index : ℝ))).toLinearMap ν) = 1 ∧
        0 < inner ℝ w u ∧
        numeratorBudget * Real.sqrt (edge - (dyadicCandidate index : ℝ)) < |inner ℝ w u| ^ 2 := by
  obtain ⟨ξmax, hξmax, hmode⟩ := integralChart_simple_modes chart w threshold numeratorBudget
    hW hS hRayleigh
  obtain ⟨index, hi0, hie, hξ⟩ := exists_positive_dyadic_candidate hedge hξmax
  exact ⟨index, hi0, hie, hmode _ (sub_pos.mpr hie) hξ⟩

end Maxwell.Defect
