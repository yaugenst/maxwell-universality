import Maxwell.Defect.EffectiveCompression
import Maxwell.Defect.BranchConstruction
import Maxwell.Defect.PhysicalBirmanSchwinger
import Maxwell.Defect.ModeBudgetCertificate

/-! End-to-end finite certification of an actually constructed simple
scalar-defect mode, with rational budgets derived from invertibility. -/
namespace Maxwell.Defect

open Spectral Spectral.Lattice Filter Topology Module.End

theorem exists_rational_inverse_budgets (H : Field →L[ℂ] Field) (hH : IsUnit H) :
    ∃ M δ : ℚ, 0 < M ∧ 0 < δ ∧ δ ≤ M ∧ ‖H‖ ≤ (M : ℝ) ∧
      ∀ x ∈ spectrum ℝ H, (δ : ℝ) ≤ |x| := by
  have hzero : (0 : ℝ) ∈ (spectrum ℝ H)ᶜ := (spectrum.zero_notMem_iff ℝ).mpr hH
  have hopen : IsOpen (spectrum ℝ H)ᶜ := (spectrum.isClosed H).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  obtain ⟨δ, hδ0, hδr⟩ := exists_rat_btwn hr
  obtain ⟨M, hM⟩ := exists_nat_gt (max ‖H‖ (δ : ℝ))
  have hnorm : ‖H‖ < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hδM : (δ : ℝ) < M := lt_of_le_of_lt (le_max_right _ _) hM
  refine ⟨M, δ, ?_, by exact_mod_cast hδ0, ?_, hnorm.le, ?_⟩
  · exact_mod_cast lt_of_le_of_lt (norm_nonneg H) hnorm
  · exact_mod_cast hδM.le
  · intro x hx
    by_contra hh
    have hxr : |x| < r := (lt_of_not_ge hh).trans hδr
    have hb : x ∈ Metric.ball (0 : ℝ) r := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hxr
    exact hball hb hx

set_option maxHeartbeats 800000 in
theorem actual_simple_mode_certifiable (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ)
    (hH : IsUnit (FiniteStencil.operator m K hK hm z))
    (u w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card)) (μ : ℝ) (threshold : ℚ)
    (hu : ‖u‖ = 1)
    (heig : FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
      m K hK hm z (ScalarDefect.coordinateWeight D) u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace
      (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        m K hK hm z (ScalarDefect.coordinateWeight D)).toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (hsourceBound : 0 < sourceBound) :
    ∃ M δ : ℚ, 0 < M ∧ 0 < δ ∧ δ ≤ M ∧
      ∃ stage : ℕ,
        modeCertificateCheck
          (FiniteStencil.effectiveCompressionMatrix (ScalarDefect.edgeEmbedding D) m z M
            (ScalarDefect.coordinateWeight D)
            (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
            (fun i => (ScalarDefect.coordinateWeight_bounds D i).2) (Nat.unpair stage).1)
          (FiniteStencil.effectiveCompressionError δ M (Nat.unpair stage).1) threshold
          (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) sourceBound
          (Nat.unpair stage).2 = true := by
  obtain ⟨M, δ, hM, hδ, hδM, hnorm, hgap⟩ := exists_rational_inverse_budgets _ hH
  refine ⟨M, δ, hM, hδ, hδM, ?_⟩
  exact FiniteStencil.effectiveCompression_mode_search_terminates
    (ScalarDefect.edgeEmbedding D) m K hK hm z M δ (ScalarDefect.coordinateWeight D)
    (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
    (fun i => (ScalarDefect.coordinateWeight_bounds D i).2) hδ hM hδM hnorm hgap
    u w μ threshold q β sourceBound hu heig hsimple hthreshold hoverlap hq hβlim hw hsourceBound

set_option maxHeartbeats 800000 in
theorem actual_simple_compression_gives_defect (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ)
    (hH : IsUnit (FiniteStencil.operator m K hK hm z))
    (u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card)) (μ : ℝ) (hμ : μ ≠ 0)
    (hu : ‖u‖ = 1)
    (heig : FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
      m K hK hm z (ScalarDefect.coordinateWeight D) u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace
      (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        m K hK hm z (ScalarDefect.coordinateWeight D)).toLinearMap μ) = 1) :
    let Hdef := ScalarDefect.perturbedOperator D (fun e => (m e : ℝ)) μ⁻¹ K hK hm
    ∃ y : Field, y ≠ 0 ∧ Hdef y = (z : ℂ) • y ∧
      Module.finrank ℂ (eigenspace Hdef.toLinearMap (z : ℂ)) = 1 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hju : realCoordinateEmbedding u ≠ 0 :=
    fun h => hu0 (realCoordinateEmbedding.injective (by simpa using h))
  obtain ⟨M, δ, hM, hδ, hδM, hnorm, hgap⟩ := exists_rational_inverse_budgets _ hH
  obtain ⟨he, hs⟩ := FiniteStencil.weightedInverseCompression_simple_complex
    (ScalarDefect.edgeEmbedding D) m K hK hm z M δ (ScalarDefect.coordinateWeight D)
    hδ hM hδM hnorm hgap u μ hu0 heig hsimple
  have hinv : FiniteStencil.operator m K hK hm z =
      electricOperator (fun e => (m e : ℝ)) K hK hm - ((z : ℝ) : ℂ) • 1 := by
    simp only [FiniteStencil.operator, Complex.ofReal_ratCast]
    rfl
  rw [hinv] at he hs
  have hspec := scalarDefect_simple_mode D (fun e => (m e : ℝ)) K (z : ℝ) μ hK hm hμ
    (hinv ▸ hH) (realCoordinateEmbedding u) hju
    (by simpa only [ScalarDefect.injection] using he)
    (by convert hs using 1; rfl)
  simpa only [Complex.ofReal_ratCast] using hspec

/-- The successful finite certificate is entirely rational. All entries
of its matrix come from the finite actual Yee stencil polynomial. -/
def scalarModeCheck (D : Finset Site) (m : Edge → ℚ) (z M δ threshold : ℚ)
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ)
    (sourceBound : ℚ) (stage : ℕ) : Bool :=
  modeCertificateCheck
    (FiniteStencil.effectiveCompressionMatrix (ScalarDefect.edgeEmbedding D) m z M
      (ScalarDefect.coordinateWeight D)
      (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
      (fun i => (ScalarDefect.coordinateWeight_bounds D i).2) (Nat.unpair stage).1)
    (FiniteStencil.effectiveCompressionError δ M (Nat.unpair stage).1) threshold
    (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) sourceBound (Nat.unpair stage).2

def HasFiniteScalarModeCertificate (D : Finset Site) (m : Edge → ℚ) (z threshold : ℚ)
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ) : Prop :=
  ∃ M δ : ℚ, 0 < M ∧ 0 < δ ∧ δ ≤ M ∧ ∃ stage,
    scalarModeCheck D m z M δ threshold q β sourceBound stage = true

/-- The rational numerator budget is checked on the certified mode itself. -/
def scalarModeBudgetCheck (D : Finset Site) (m : Edge → ℚ) (z M δ threshold budget : ℚ)
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ)
    (sourceBound : ℚ) (stage : ℕ) : Bool :=
  modeBudgetCheck
    (FiniteStencil.effectiveCompressionMatrix (ScalarDefect.edgeEmbedding D) m z M
      (ScalarDefect.coordinateWeight D)
      (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
      (fun i => (ScalarDefect.coordinateWeight_bounds D i).2) (Nat.unpair stage).1)
    (FiniteStencil.effectiveCompressionError δ M (Nat.unpair stage).1) threshold
    (q (Nat.unpair stage).1) (β (Nat.unpair stage).1) sourceBound budget (Nat.unpair stage).2

set_option maxHeartbeats 800000 in
theorem actual_simple_mode_budget_certifiable (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ)
    (hH : IsUnit (FiniteStencil.operator m K hK hm z))
    (u w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card)) (μ : ℝ)
    (threshold budget : ℚ) (hu : ‖u‖ = 1)
    (heig : FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
      m K hK hm z (ScalarDefect.coordinateWeight D) u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace
      (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        m K hK hm z (ScalarDefect.coordinateWeight D)).toLinearMap μ) = 1)
    (hthreshold : (threshold : ℝ) < μ) (hoverlap : inner ℝ w u ≠ 0)
    (hbudget : 0 ≤ budget) (hmargin : (budget : ℝ) < |inner ℝ w u| ^ 2 / 64)
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (hsourceBound : 0 < sourceBound) :
    ∃ M δ : ℚ, 0 < M ∧ 0 < δ ∧ δ ≤ M ∧
      ‖FiniteStencil.operator m K hK hm z‖ ≤ (M : ℝ) ∧
      (∀ x ∈ spectrum ℝ (FiniteStencil.operator m K hK hm z), (δ : ℝ) ≤ |x|) ∧
      ∃ stage : ℕ, scalarModeBudgetCheck D m z M δ threshold budget q β sourceBound stage = true := by
  obtain ⟨M, δ, hM, hδ, hδM, hnorm, hgap⟩ := exists_rational_inverse_budgets _ hH
  refine ⟨M, δ, hM, hδ, hδM, hnorm, hgap, ?_⟩
  exact modeBudget_search_terminates
    (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
      m K hK hm z (ScalarDefect.coordinateWeight D)) u w μ
    (FiniteStencil.effectiveCompressionMatrix (ScalarDefect.edgeEmbedding D) m z M
      (ScalarDefect.coordinateWeight D)
      (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
      (fun i => (ScalarDefect.coordinateWeight_bounds D i).2))
    (FiniteStencil.effectiveCompressionError δ M) threshold budget q β sourceBound
    hu heig hsimple hthreshold hoverlap hbudget hmargin
    (FiniteStencil.effectiveCompressionMatrix_symmetric _ m K hK hm z M _ _ _)
    (fun k => FiniteStencil.effectiveCompressionError_nonneg δ M k hδ hM hδM)
    (FiniteStencil.effectiveCompressionMatrix_tendsto _ m K hK hm z M δ _ _ _
      hδ hM hδM hnorm hgap)
    (FiniteStencil.effectiveCompressionError_tendsto δ M hδ hM hδM)
    hq hβlim hw hsourceBound

set_option maxHeartbeats 800000 in
theorem scalarModeBudgetCheck_sound (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ threshold budget : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖FiniteStencil.operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (FiniteStencil.operator m K hK hm z), (δ : ℝ) ≤ |x|)
    (w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (stage : ℕ)
    (hcheck : scalarModeBudgetCheck D m z M δ threshold budget q β sourceBound stage = true) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card),
      ‖u‖ = 1 ∧ FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        m K hK hm z (ScalarDefect.coordinateWeight D) u = μ • u ∧
      (threshold : ℝ) < μ ∧ Module.finrank ℝ (eigenspace
        (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
          m K hK hm z (ScalarDefect.coordinateWeight D)).toLinearMap μ) = 1 ∧
      (budget : ℝ) < |inner ℝ w u| ^ 2 := by
  unfold scalarModeBudgetCheck modeBudgetCheck at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i c a hca
    apply modeBudget_sound c a _ _ threshold _ _ sourceBound budget _ w
      (FiniteStencil.weightedInverseCompression_symmetric _ m K hK hm z _)
      _ (hq _) hw hcheck
    rw [norm_sub_rev]
    exact FiniteStencil.effectiveCompressionMatrix_error _ m K hK hm z M δ _ _ _ _
      hδ hM hδM hnorm hgap

set_option maxHeartbeats 1000000 in
/-- The analytic expansion and proved coherent Rayleigh estimate select
an actual dyadic simple defect mode and an accepted finite certificate.
Simplicity and successful search are conclusions of this theorem. -/
theorem sqrt_expansion_certified_scalar_defect (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (S : ℝ → EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card) →L[ℝ]
      EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (c C r edge numeratorBudget : ℝ) (threshold : ℚ)
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r) (hedge : 0 < edge) (hthreshold : 0 ≤ threshold)
    (hS : ∀ ξ, (S ξ).toLinearMap.IsSymmetric)
    (hRayleigh : (threshold : ℝ) * ‖w‖ ^ 2 < inner ℝ w (S 0 w))
    (hexp : ∀ ξ, 0 < ξ → ξ ≤ r →
      ‖S 0 - S ξ - (c * Real.sqrt ξ) • InnerProductSpace.rankOne ℝ w w‖ ≤ C * ξ)
    (hbind : ∀ z : ℚ, 0 < (z : ℝ) → (z : ℝ) < edge →
      S (edge - (z : ℝ)) = FiniteStencil.weightedInverseCompression
        (ScalarDefect.edgeEmbedding D) m K hK hm z (ScalarDefect.coordinateWeight D))
    (hunit : ∀ z : ℚ, 0 < (z : ℝ) → (z : ℝ) < edge →
      IsUnit (FiniteStencil.operator m K hK hm z))
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hβlim : Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (hsourceBound : 0 < sourceBound) :
    ∃ index : ℕ, 0 < (dyadicCandidate index : ℝ) ∧ (dyadicCandidate index : ℝ) < edge ∧
      ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card),
        ‖u‖ = 1 ∧ S (edge - (dyadicCandidate index : ℝ)) u = μ • u ∧
        (threshold : ℝ) < μ ∧
        Module.finrank ℝ (eigenspace (S (edge - (dyadicCandidate index : ℝ))).toLinearMap μ) = 1 ∧
        0 < inner ℝ w u ∧
        numeratorBudget * Real.sqrt (edge - (dyadicCandidate index : ℝ)) < |inner ℝ w u| ^ 2 ∧
        HasFiniteScalarModeCertificate D m (dyadicCandidate index) threshold q β sourceBound ∧
        ∃ y : Field, y ≠ 0 ∧
          ScalarDefect.perturbedOperator D (fun e => (m e : ℝ)) μ⁻¹ K hK hm y =
            (dyadicCandidate index : ℂ) • y ∧
          Module.finrank ℂ (eigenspace
            (ScalarDefect.perturbedOperator D (fun e => (m e : ℝ)) μ⁻¹ K hK hm).toLinearMap
              (dyadicCandidate index : ℂ)) = 1 := by
  obtain ⟨index, hiz, hie, μ, u, hu, heig, hμ, hsimple, hover, hnum⟩ :=
    sqrt_expansion_dyadic_simple_mode S w c C r edge threshold numeratorBudget
      hc hC hr hedge hS hRayleigh hexp
  have hi := hbind (dyadicCandidate index) hiz hie
  have heig' := heig
  have hsimple' := hsimple
  rw [hi] at heig' hsimple'
  have hH := hunit (dyadicCandidate index) hiz hie
  have hcert := actual_simple_mode_certifiable D m K hK hm (dyadicCandidate index) hH
    u w μ threshold hu heig' hsimple' hμ hover.ne' q β sourceBound hq hβlim hw hsourceBound
  have hμ0 : μ ≠ 0 := (lt_of_le_of_lt (by exact_mod_cast hthreshold) hμ).ne'
  have hphysical := actual_simple_compression_gives_defect D m K hK hm
    (dyadicCandidate index) hH u μ hμ0 hu heig' hsimple'
  exact ⟨index, hiz, hie, μ, u, hu, heig, hμ, hsimple, hover, hnum, hcert, hphysical⟩

end Maxwell.Defect
