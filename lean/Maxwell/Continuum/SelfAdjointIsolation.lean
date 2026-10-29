import Maxwell.Continuum.SelfAdjointClosedRange

/-! Closed range gives an actual punctured spectral gap. This statement is
local in the full real line, not merely relative to a counting window. -/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) [CompleteSpace A.ker]

include hA

theorem kernel_shift_norm_bound
    (hclosed : IsClosed (A.toFun.range : Set H))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ u : A.domain, (u : H) ∈ A.kerᗮ → ‖(u : H)‖ ≤ C * ‖A u‖)
    (σ : ℝ) (hσpos : 0 < |σ|) (hσsmall : |σ| < (2 * C)⁻¹) (u : A.domain) :
    ‖(u : H)‖ ≤ (|σ|⁻¹ + 2 * C) * ‖shift A σ u‖ := by
  let K := A.ker
  let F := kernelRestriction A
  let g : K := K.orthogonalProjectionOnto u
  let t : Kᗮ := Kᗮ.orthogonalProjectionOnto u
  let f := shift A σ u
  have hAu : A u ∈ Kᗮ := by
    rw [← range_eq_kernel_orthogonal A hA hclosed]
    exact ⟨u, rfl⟩
  have hAg : K.orthogonalProjectionOnto (A u) = 0 :=
    K.orthogonalProjectionOnto_eq_zero_iff.mpr hAu
  have hAt : Kᗮ.orthogonalProjectionOnto (A u) = (⟨A u, hAu⟩ : Kᗮ) :=
    Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self (⟨A u, hAu⟩ : Kᗮ)
  have hfg : K.orthogonalProjectionOnto f = -(σ : ℂ) • g := by
    change K.orthogonalProjectionOnto (shift A σ u) =
      -(σ : ℂ) • K.orthogonalProjectionOnto (u : H)
    rw [shift_apply, map_sub, map_smul, hAg, zero_sub, neg_smul]
    rfl
  have hft : (⟨A u, hAu⟩ : Kᗮ) = Kᗮ.orthogonalProjectionOnto f + (σ : ℂ) • t := by
    change (⟨A u, hAu⟩ : Kᗮ) = Kᗮ.orthogonalProjectionOnto (shift A σ u) +
      (σ : ℂ) • Kᗮ.orthogonalProjectionOnto (u : H)
    rw [shift_apply, map_sub, map_smul, hAt]
    exact (sub_add_cancel (⟨A u, hAu⟩ : Kᗮ) ((σ : ℂ) • t)).symm
  have hgraw : |σ| * ‖g‖ ≤ ‖f‖ := by
    have h := K.norm_orthogonalProjectionOnto_apply_le f
    rw [hfg, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hg : ‖g‖ ≤ |σ|⁻¹ * ‖f‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hσpos).mpr (by simpa only [mul_comm] using hgraw)
  have htA : ‖t‖ ≤ C * ‖A u‖ := by
    have h := hbound (InvariantRestriction.Data.highInclusion A K (F.domainHighProjection u))
      t.property
    have ha := congrArg Subtype.val (F.highProjection_action hA u)
    have hb := ha.trans (congrArg Subtype.val hAt)
    change A (InvariantRestriction.Data.highInclusion A K (F.domainHighProjection u)) = A u at hb
    change ‖t‖ ≤ C * ‖A (InvariantRestriction.Data.highInclusion A K
      (F.domainHighProjection u))‖ at h
    exact h.trans_eq (congrArg (fun z : H => C * ‖z‖) hb)
  have hAuNorm : ‖A u‖ ≤ ‖f‖ + |σ| * ‖t‖ := by
    calc
      ‖A u‖ = ‖Kᗮ.orthogonalProjectionOnto f + (σ : ℂ) • t‖ :=
        congrArg (fun z : Kᗮ => ‖z‖) hft
      _ ≤ ‖Kᗮ.orthogonalProjectionOnto f‖ + ‖(σ : ℂ) • t‖ := norm_add_le _ _
      _ ≤ ‖f‖ + |σ| * ‖t‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (Kᗮ.norm_orthogonalProjectionOnto_apply_le f) le_rfl
  have hsmall : C * |σ| < 1 / 2 := by
    have h : |σ| * (2 * C) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp
        (by simpa only [one_div] using hσsmall)
    nlinarith
  have ht : ‖t‖ ≤ 2 * C * ‖f‖ := by
    have h1 := htA.trans (mul_le_mul_of_nonneg_left hAuNorm hC.le)
    have h2 := mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg t)
    nlinarith
  calc
    ‖(u : H)‖ = ‖(g : H) + (t : H)‖ :=
      (congrArg norm (InvariantRestriction.Data.decomposition (K := K) (u : H))).symm
    _ ≤ ‖g‖ + ‖t‖ := norm_add_le _ _
    _ ≤ |σ|⁻¹ * ‖f‖ + 2 * C * ‖f‖ := add_le_add hg ht
    _ = (|σ|⁻¹ + 2 * C) * ‖shift A σ u‖ := by ring

/-- Every self-adjoint closed-range operator has a punctured neighborhood
of zero consisting entirely of genuine bounded resolvent points. -/
theorem exists_punctured_gap (hclosed : IsClosed (A.toFun.range : Set H)) :
    ∃ η : ℝ, 0 < η ∧ ∀ σ : ℝ, 0 < |σ| → |σ| < η → σ ∉ realSpectrum A := by
  obtain ⟨C, hC, hbound⟩ := kernel_complement_bound A hA hclosed
  refine ⟨(2 * C)⁻¹, by positivity, ?_⟩
  intro σ hσpos hσsmall
  have hden : 0 < |σ|⁻¹ + 2 * C := by positivity
  apply (not_mem_realSpectrum A σ).mpr
  refine ⟨BoundedInverse.ofLowerBound (shift_selfAdjoint A σ hA)
    (inv_pos.mpr hden) ?_⟩
  intro u
  have h := kernel_shift_norm_bound A hA hclosed hC hbound σ hσpos hσsmall u
  have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hden.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hden), one_mul] using hmul

end Maxwell.Continuum.SelfAdjointResolvent
