import Maxwell.Defect.FixedDefectSelection

/-! Selection by the accepted finite certificate, including the
quantitative numerator condition used by the uniform Green theorem. -/
namespace Maxwell.Defect
open Spectral Spectral.Lattice Filter Topology Module.End

/-- This gate uses only rational arithmetic. A certified upper edge
enclosure turns it into the strict physical square-root numerator bound. -/
def numeratorBudgetCheck (upper z constant budget : ℚ) : Bool :=
  decide (0 ≤ constant ∧ 0 < budget ∧ constant ^ 2 * (upper - z) < budget ^ 2)

theorem numeratorBudgetCheck_sound (upper z constant budget : ℚ) (edge K : ℝ)
    (hupper : edge ≤ (upper : ℝ)) (hK : K ≤ (constant : ℝ))
    (hz : (z : ℝ) ≤ edge)
    (hcheck : numeratorBudgetCheck upper z constant budget = true) :
    K * Real.sqrt (edge - (z : ℝ)) < (budget : ℝ) := by
  obtain ⟨hc, hb, hsq⟩ := of_decide_eq_true hcheck
  have hc' : (0 : ℝ) ≤ constant := by exact_mod_cast hc
  have hb' : (0 : ℝ) < budget := by exact_mod_cast hb
  have hsq' : (constant : ℝ) ^ 2 * ((upper : ℝ) - z) < (budget : ℝ) ^ 2 := by
    exact_mod_cast hsq
  have he : 0 ≤ edge - (z : ℝ) := sub_nonneg.mpr hz
  have hupper' : (constant : ℝ) ^ 2 * (edge - (z : ℝ)) < (budget : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)).trans_lt hsq'
  have hroot : (constant : ℝ) * Real.sqrt (edge - (z : ℝ)) < (budget : ℝ) := by
    nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (edge - (z : ℝ))]
  exact (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _)).trans_lt hroot

set_option maxHeartbeats 1000000 in
/-- The mode returned by soundness of the accepted rational certificate
satisfies the Green numerator budget. The analytic mode is used only to
prove termination; the final mode is the one certified by the checker. -/
theorem sqrt_expansion_finite_selection (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (S : ℝ → EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card) →L[ℝ]
      EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (c C r edge numeratorBudget cutoff : ℝ) (threshold : ℚ)
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r) (hedge : 0 < edge)
    (hcutoff : 0 < cutoff) (hthreshold : 0 ≤ threshold)
    (hS : ∀ ξ, (S ξ).toLinearMap.IsSymmetric)
    (hRayleigh : (threshold : ℝ) * ‖w‖ ^ 2 < inner ℝ w (S 0 w))
    (hexp : ∀ ξ, 0 < ξ → ξ ≤ r →
      ‖S 0 - S ξ - (c * Real.sqrt ξ) • InnerProductSpace.rankOne ℝ w w‖ ≤ C * ξ)
    (hbind : ∀ z : ℚ, 0 < (z : ℝ) → (z : ℝ) < edge →
      S (edge - (z : ℝ)) = FiniteStencil.weightedInverseCompression
        (ScalarDefect.edgeEmbedding D) m K hK hm z (ScalarDefect.coordinateWeight D))
    (hunit : ∀ z : ℚ, 0 < (z : ℝ) → (z : ℝ) < edge →
      edge - (z : ℝ) < cutoff → IsUnit (FiniteStencil.operator m K hK hm z))
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (hsourceBound : 0 < sourceBound) :
    ∃ index : ℕ, 0 < (dyadicCandidate index : ℝ) ∧ (dyadicCandidate index : ℝ) < edge ∧
      edge - (dyadicCandidate index : ℝ) < cutoff ∧
      ∃ M δ budget : ℚ, 0 < M ∧ 0 < δ ∧ δ ≤ M ∧ 0 < budget ∧
        ‖FiniteStencil.operator m K hK hm (dyadicCandidate index)‖ ≤ (M : ℝ) ∧
        (∀ x ∈ spectrum ℝ (FiniteStencil.operator m K hK hm (dyadicCandidate index)),
          (δ : ℝ) ≤ |x|) ∧
        numeratorBudget * Real.sqrt (edge - (dyadicCandidate index : ℝ)) < (budget : ℝ) ∧
        ∃ stage : ℕ,
          scalarModeBudgetCheck D m (dyadicCandidate index) M δ threshold budget q β
            sourceBound stage = true ∧
          ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card),
            ‖u‖ = 1 ∧ S (edge - (dyadicCandidate index : ℝ)) u = μ • u ∧
            (threshold : ℝ) < μ ∧
            Module.finrank ℝ (eigenspace
              (S (edge - (dyadicCandidate index : ℝ))).toLinearMap μ) = 1 ∧
            (budget : ℝ) < |inner ℝ w u| ^ 2 ∧
            ∃ y : Field, y ≠ 0 ∧
              ScalarDefect.perturbedOperator D (fun e => (m e : ℝ)) μ⁻¹ K hK hm y =
                (dyadicCandidate index : ℂ) • y ∧
              Module.finrank ℂ (eigenspace
                (ScalarDefect.perturbedOperator D (fun e => (m e : ℝ)) μ⁻¹ K hK hm).toLinearMap
                  (dyadicCandidate index : ℂ)) = 1 := by
  obtain ⟨ξmax, hξmax, hmode⟩ := sqrt_expansion_simple_modes S w c C r threshold
    (64 * max numeratorBudget 0 + 1) hc hC hr hS hRayleigh hexp
  obtain ⟨index, hiz, hie, hξ⟩ := exists_positive_dyadic_candidate hedge (lt_min hξmax hcutoff)
  have hξ0 : 0 < edge - (dyadicCandidate index : ℝ) := sub_pos.mpr hie
  obtain ⟨ν, v, hv, hev, hν, hvsimple, hvover, hvbudget⟩ :=
    hmode _ hξ0 (hξ.trans_le (min_le_left _ _))
  have hroom : max numeratorBudget 0 * Real.sqrt (edge - (dyadicCandidate index : ℝ)) <
      |inner ℝ w v| ^ 2 / 64 := by
    nlinarith [Real.sqrt_pos.mpr hξ0]
  obtain ⟨budget, hbudgetlo, hbudgethi⟩ := exists_rat_btwn hroom
  have hbudgetpos : (0 : ℚ) < budget := by
    have : (0 : ℝ) < budget := lt_of_le_of_lt
      (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) hbudgetlo
    exact_mod_cast this
  have hbudget : numeratorBudget * Real.sqrt (edge - (dyadicCandidate index : ℝ)) <
      (budget : ℝ) := (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.sqrt_nonneg _)).trans_lt hbudgetlo
  have hi := hbind (dyadicCandidate index) hiz hie
  have hH := hunit (dyadicCandidate index) hiz hie (hξ.trans_le (min_le_right _ _))
  rw [hi] at hev hvsimple
  obtain ⟨M, δ, hM, hδ, hδM, hnorm, hgap, stage, hcheck⟩ :=
    actual_simple_mode_budget_certifiable D m K hK hm (dyadicCandidate index) hH
      v w ν threshold budget hv hev hvsimple hν hvover.ne' hbudgetpos.le hbudgethi
      q β sourceBound hq hβlim hw hsourceBound
  obtain ⟨μ, u, hu, he, hμ, hsimple, hover⟩ := scalarModeBudgetCheck_sound D m K hK hm
    (dyadicCandidate index) M δ threshold budget hδ hM hδM hnorm hgap w q β sourceBound
      hq hw stage hcheck
  have hμ0 : μ ≠ 0 := (lt_of_le_of_lt (by exact_mod_cast hthreshold) hμ).ne'
  have hphysical := actual_simple_compression_gives_defect D m K hK hm
    (dyadicCandidate index) hH u μ hμ0 hu he hsimple
  rw [← hi] at he hsimple
  exact ⟨index, hiz, hie, hξ.trans_le (min_le_right _ _), M, δ, budget, hM, hδ, hδM,
    hbudgetpos, hnorm, hgap, hbudget, stage, hcheck, μ, u, hu, he, hμ, hsimple, hover, hphysical⟩

end Maxwell.Defect
