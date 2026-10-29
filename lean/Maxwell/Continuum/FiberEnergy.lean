import Maxwell.Continuum.FiberReflectionGraph

/-! Exact complex energy shifts of the maximal fiber graph, and reality of
its eigenvalues at real momentum. Domain membership is transferred by the
graph identity, not postulated to be independent of energy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FreeFiber

theorem block_energy_add (p : Momentum) (E F : ℂ) (v : Polarization) :
    block p F v = block p E v + (E - F) • v := by
  apply PiLp.ext
  intro j
  simp only [FiberReflection.block_coordinate, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem material_graph_energy_shift (q : Momentum) (E F : ℂ) (ρ : ℝ)
    (u v : FiberSpace) (h : (u, v) ∈ (materialFiber q E ρ).graph) :
    (u, v + (E - F) • u) ∈ (materialFiber q F ρ).graph := by
  have hg := (Bloch.materialFiber_graph_iff _ _ _ _ _).mp h
  apply (Bloch.materialFiber_graph_iff _ _ _ _ _).mpr
  apply (operator_graph_iff _ _ _ _).mpr
  intro ν
  rw [block_energy_add (aliasMomentum q ν) E F (u ν)]
  have heq := (operator_graph_iff _ _ _ _).mp hg ν
  rw [heq]
  change (v ν + (ρ : ℂ) • potential u ν) + (E - F) • u ν =
    (v ν + (E - F) • u ν) + (ρ : ℂ) • potential u ν
  abel

theorem selfAdjoint_eigenvalue_im_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (u : A.domain) (hu : (u : H) ≠ 0) (z : ℂ) (he : A u = z • (u : H)) : z.im = 0 := by
  have hs : A.IsFormalAdjoint A := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hA] using
      LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have hi := hs u u
  rw [he, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at hi
  rw [← RCLike.ofReal_pow] at hi
  change (starRingEnd ℂ) z * ((‖(u : H)‖ ^ 2 : ℝ) : ℂ) =
    z * ((‖(u : H)‖ ^ 2 : ℝ) : ℂ) at hi
  have him := congrArg Complex.im hi
  simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add] at him
  have hn : 0 < ‖(u : H)‖ := norm_pos_iff.mpr hu
  nlinarith [sq_pos_of_pos hn]

/-- Every actual maximal-domain eigenvalue is real when the momentum and
the scalar potential are real. -/
theorem material_kernel_energy_im_zero (q : Fin 3 → ℝ) (E : ℂ) (ρ : ℝ)
    (h : ∃ u : FiberSpace, u ≠ 0 ∧ (u, 0) ∈ (materialFiber (realMomentum q) E ρ).graph) :
    E.im = 0 := by
  obtain ⟨u, hu, hgraph⟩ := h
  have hg := material_graph_energy_shift (realMomentum q) E 0 ρ u 0 hgraph
  simp only [sub_zero, zero_add] at hg
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨x, hx, hMx⟩ := hg
  apply selfAdjoint_eigenvalue_im_zero (materialFiber (realMomentum q) 0 ρ)
    (real_materialFiber_selfAdjoint q 0 ρ) x (by exact hx ▸ hu) E
  exact hMx.trans (congrArg (fun v : FiberSpace => E • v) hx.symm)

theorem scaledMomentum_real (t : Fin 3 → ℝ) :
    scaledMomentum (realMomentum t) = realMomentum (fun j => backgroundAmplitude * t j) := by
  funext j
  simp only [scaledMomentum, realMomentum, Complex.ofReal_mul]

theorem actual_kernel_scaledEnergy_im_zero (t : Fin 3 → ℝ) (e : ℂ)
    (h : ∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum (realMomentum t))
        (totalEnergy e) backgroundAmplitude).graph) : e.im = 0 := by
  rw [scaledMomentum_real] at h
  have him := material_kernel_energy_im_zero (fun j => backgroundAmplitude * t j)
    (totalEnergy e) backgroundAmplitude h
  simp only [totalEnergy, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, zero_add, add_zero] at him
  exact (mul_eq_zero.mp him).resolve_left backgroundAmplitude_pos.ne'

end Maxwell.Continuum.FreeFiber
