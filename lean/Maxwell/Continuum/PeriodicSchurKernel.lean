import Maxwell.Continuum.PeriodicBandDomain

/-! The finite Schur kernel criterion is equivalent to a literal nonzero
eigenvector in the full maximal fiber graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation

theorem schur_nonzero_iff_actual (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    (∃ x : clusterSpace, x ≠ 0 ∧ finiteSchur t e ht he x = 0) ↔
      ∃ u : FiberSpace, u ≠ 0 ∧
        (u, 0) ∈ (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph := by
  let T := fiberSchurKernelEquiv t e ht he
  constructor
  · rintro ⟨x, hx0, hx⟩
    let x' : FiniteKernel t e ht he := ⟨x, hx⟩
    have hx' : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    have hy : T x' ≠ 0 := T.map_ne_zero_iff.mpr hx'
    refine ⟨(T x').val.val, ?_, ?_⟩
    · intro h
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · rw [LinearPMap.mem_graph_iff]
      exact ⟨(T x').val, rfl, (T x').property⟩
  · rintro ⟨u, hu0, hu⟩
    rw [LinearPMap.mem_graph_iff] at hu
    obtain ⟨x, hx, hMx⟩ := hu
    let y : ActualKernel t e := ⟨x, hMx⟩
    have hy : y ≠ 0 := by
      intro h
      have hv : x.val = 0 := congrArg (fun a : ActualKernel t e => a.val.val) h
      exact hu0 (hx.symm.trans hv)
    have hz : T.symm y ≠ 0 := T.symm.map_ne_zero_iff.mpr hy
    refine ⟨(T.symm y).val, ?_, (T.symm y).property⟩
    intro h
    exact hz (Subtype.ext h)

theorem schurExtension_nonzero_iff_actual (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    (∃ x : clusterSpace, x ≠ 0 ∧ finiteSchurExtension (t, e) x = 0) ↔
      ∃ u : FiberSpace, u ≠ 0 ∧
        (u, 0) ∈ (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph := by
  rw [finiteSchurExtension_eq (t, e) ⟨ht, he⟩]
  exact schur_nonzero_iff_actual t e ht he

end Maxwell.Continuum.PeriodicBand
