import Maxwell.Spectral.AnalyticEigenbranch

/-! A single constructed analytic branch carries its eigenvector, projector,
regular resolvent and inversion symmetry. Keeping these witnesses together
allows the differentiated eigenpair and the pole integral to use the same
scalar dispersion. -/

namespace Maxwell.Spectral.AnalyticEigenbranch

noncomputable section

variable {W E : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_even_analytic_resolvent
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2))
    (J : E ≃L[ℂ] E)
    (hsym : ∀ (w : W) (z : ℂ × E),
      A (-w) (z.1, J z.2) = ((A w z).1, J (A w z).2)) :
    ∃ value : W → ℂ, ∃ u : W → ℂ × E,
    ∃ P : W → (ℂ × E) →L[ℂ] (ℂ × E),
    ∃ R : W × ℂ → (ℂ × E) →L[ℂ] (ℂ × E),
      value 0 = energy ∧ u 0 = (1, 0) ∧
      P 0 = (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      AnalyticAt ℂ R (0, 0) ∧
      (∀ w, (u w).1 = 1 ∧ u w ≠ 0) ∧
      (∀ᶠ w in nhds (0 : W),
        A w (u w) = value w • u w ∧
        value (-w) = value w ∧ u (-w) = (1, J (u w).2) ∧
        P w * P w = P w ∧
        A w * P w = value w • P w ∧ P w * A w = value w • P w ∧
        LinearMap.range (P w).toLinearMap = Submodule.span ℂ ({u w} : Set (ℂ × E))) ∧
      (∀ᶠ z in nhds ((0, 0) : W × ℂ), value z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • 1).IsInvertible ∧
        (A z.1 - (energy + z.2) • 1).inverse =
          (value z.1 - (energy + z.2))⁻¹ • P z.1 + R z) := by
  obtain ⟨value, u, P, hv0, hu0, hP0, hv, hu, hP, hnorm, hgood, hunique⟩ :=
    exists_analytic_eigenprojection_with_uniqueness A energy B hA hcenter
  have hsolve : ∀ᶠ w in nhds (0 : W), A w (u w) = value w • u w := by
    filter_upwards [hgood] with w hw
    exact hw.1
  have heven := eigenpair_inversion_of_local_uniqueness A energy value u J
    hv0 hu0 hv.continuousAt hu.continuousAt (fun w => (hnorm w).1)
    hsolve hunique hsym
  let R := fun z : W × ℂ => regularResolvent (A z.1) (P z.1) (energy + z.2)
  have hi0 : (A 0 - energy • 1 + P 0).IsInvertible := by
    rw [hP0]
    exact augmented_center_invertible (A 0) energy B hcenter
  have hg : ∀ᶠ w in nhds (0 : W),
      P w * P w = P w ∧ A w * P w = value w • P w ∧
      P w * A w = value w • P w := by
    filter_upwards [hgood] with w hw
    exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  obtain ⟨hR, hres⟩ := regular_resolvent_near_eigenprojection A value P energy hA hP hi0 hg
  refine ⟨value, u, P, R, hv0, hu0, hP0, hv, hu, hP, hR, hnorm, ?_, hres⟩
  filter_upwards [hgood, heven] with w hw hs
  exact ⟨hw.1, hs.1, hs.2, hw.2⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Transport all witnesses together, preserving the same even scalar branch
in the eigenpair equation and the physical resolvent decomposition. -/
theorem exists_even_analytic_resolvent_in_coordinates
    (A : W → H →L[ℂ] H) (energy : ℂ)
    (e : (ℂ × E) ≃L[ℂ] H) (B J : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E,
      A 0 (e z) = e (energy * z.1, energy • z.2 + B z.2))
    (hsym : ∀ (w : W) (z : ℂ × E),
      A (-w) (e (z.1, J z.2)) =
        e ((e.symm (A w (e z))).1, J (e.symm (A w (e z))).2)) :
    ∃ value : W → ℂ, ∃ u : W → H,
    ∃ P : W → H →L[ℂ] H, ∃ R : W × ℂ → H →L[ℂ] H,
      value 0 = energy ∧ u 0 = e (1, 0) ∧
      P 0 = e.conjContinuousAlgEquiv
        ((ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0)) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      AnalyticAt ℂ R (0, 0) ∧
      (∀ w, (e.symm (u w)).1 = 1 ∧ u w ≠ 0) ∧
      (∀ᶠ w in nhds (0 : W),
        A w (u w) = value w • u w ∧ value (-w) = value w ∧
        P w * P w = P w ∧ A w * P w = value w • P w ∧
        P w * A w = value w • P w) ∧
      (∀ᶠ z in nhds ((0, 0) : W × ℂ), value z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • 1).IsInvertible ∧
        (A z.1 - (energy + z.2) • 1).inverse =
          (value z.1 - (energy + z.2))⁻¹ • P z.1 + R z) := by
  let g := e.conjContinuousAlgEquiv
  let Ac := fun w => g.symm (A w)
  have hc : AnalyticAt ℂ Ac 0 :=
    (g.symm.toContinuousLinearEquiv.analyticAt (A 0)).comp hA
  have h0 (z : ℂ × E) : Ac 0 z = (energy * z.1, energy • z.2 + B z.2) := by
    change e.symm (A 0 (e z)) = _
    rw [hcenter]
    exact e.symm_apply_apply _
  have hs (w : W) (z : ℂ × E) :
      Ac (-w) (z.1, J z.2) = ((Ac w z).1, J (Ac w z).2) := by
    change e.symm (A (-w) (e (z.1, J z.2))) = _
    rw [hsym, e.symm_apply_apply]
    rfl
  obtain ⟨value, u, P, R, hv0, hu0, hP0, hv, hu, hP, hR, hnorm, hgood, hres⟩ :=
    exists_even_analytic_resolvent Ac energy B hc h0 J hs
  refine ⟨value, fun w => e (u w), fun w => g (P w), fun z => g (R z),
    hv0, congrArg e hu0, congrArg g hP0, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (e.analyticAt (u 0)).comp hu
  · exact (g.toContinuousLinearEquiv.analyticAt (P 0)).comp hP
  · exact (g.toContinuousLinearEquiv.analyticAt (R (0, 0))).comp hR
  · intro w
    refine ⟨by simpa only [e.symm_apply_apply] using (hnorm w).1, ?_⟩
    intro hz
    exact (hnorm w).2 (e.injective (hz.trans e.map_zero.symm))
  · filter_upwards [hgood] with w hw
    refine ⟨?_, hw.2.1, ?_, ?_, ?_⟩
    · have h := hw.1
      change e.symm (A w (e (u w))) = value w • u w at h
      simpa only [e.apply_symm_apply, map_smul] using congrArg e h
    · simpa only [map_mul] using congrArg g hw.2.2.2.1
    · simpa [Ac] using congrArg g hw.2.2.2.2.1
    · simpa [Ac] using congrArg g hw.2.2.2.2.2.1
  · filter_upwards [hres] with z hz
    intro hne
    obtain ⟨hi, heq⟩ := hz hne
    have hconj : g (Ac z.1 - (energy + z.2) • 1) =
        A z.1 - (energy + z.2) • 1 := by simp [Ac]
    refine ⟨?_, ?_⟩
    · rw [← hconj]
      exact (conjugation_isInvertible e _).mpr hi
    · have heq' := congrArg g heq
      rw [← conjugation_inverse e, hconj] at heq'
      simpa only [map_add, map_smul] using heq'

end
end Maxwell.Spectral.AnalyticEigenbranch
