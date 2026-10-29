import Maxwell.Continuum.FiberReflectionBlock

/-! An actual unitary reflection on the infinite alias Hilbert space and the
exact material-potential intertwining. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberReflection

open FreeFiber

def fiber (j : Fin 3) : FiberSpace ≃ₗᵢ[ℂ] FiberSpace where
  toFun u := ⟨fun ν => polarization j (u (aliasEquiv j ν)), by
    apply memℓp_gen
    simp only [LinearIsometryEquiv.norm_map]
    exact (aliasEquiv j).summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  invFun u := ⟨fun ν => polarization j (u (aliasEquiv j ν)), by
    apply memℓp_gen
    simp only [LinearIsometryEquiv.norm_map]
    exact (aliasEquiv j).summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  left_inv u := by
    apply Subtype.ext
    funext ν
    change polarization j (polarization j (u (aliasEquiv j (aliasEquiv j ν)))) = u ν
    rw [alias_involutive, polarization_involutive]
  right_inv u := by
    apply Subtype.ext
    funext ν
    change polarization j (polarization j (u (aliasEquiv j (aliasEquiv j ν)))) = u ν
    rw [alias_involutive, polarization_involutive]
  map_add' u v := by
    apply Subtype.ext
    funext ν
    exact (polarization j).map_add (u (aliasEquiv j ν)) (v (aliasEquiv j ν))
  map_smul' c u := by
    apply Subtype.ext
    funext ν
    exact (polarization j).map_smul c (u (aliasEquiv j ν))
  norm_map' u := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    change (∑' ν, ‖polarization j (u (aliasEquiv j ν))‖ ^ (2 : ENNReal).toReal) ^
      (1 / (2 : ENNReal).toReal) = _
    simp only [LinearIsometryEquiv.norm_map]
    exact congrArg (fun r : ℝ => r ^ (1 / (2 : ENNReal).toReal))
      ((aliasEquiv j).tsum_eq (fun ν : Alias => ‖u ν‖ ^ (2 : ENNReal).toReal))

@[simp] theorem fiber_apply (j : Fin 3) (u : FiberSpace) (ν : Alias) :
    fiber j u ν = polarization j (u (aliasEquiv j ν)) := rfl

theorem fiber_involutive (j : Fin 3) (u : FiberSpace) : fiber j (fiber j u) = u :=
  (fiber j).left_inv u

theorem alias_add_unit (j k : Fin 3) (ν : Alias) :
    aliasEquiv j (ν + unitAlias k) =
      if k = j then aliasEquiv j ν - unitAlias k else aliasEquiv j ν + unitAlias k := by
  funext l
  by_cases hk : k = j <;> by_cases hl : l = j <;> by_cases hlk : l = k <;>
    simp_all [aliasEquiv, unitAlias, Pi.add_apply, Pi.sub_apply]
  ring

theorem alias_sub_unit (j k : Fin 3) (ν : Alias) :
    aliasEquiv j (ν - unitAlias k) =
      if k = j then aliasEquiv j ν + unitAlias k else aliasEquiv j ν - unitAlias k := by
  funext l
  by_cases hk : k = j <;> by_cases hl : l = j <;> by_cases hlk : l = k <;>
    simp_all [aliasEquiv, unitAlias, Pi.add_apply, Pi.sub_apply]

/-- The six-neighbor scalar potential commutes with polar-vector reflection. -/
theorem potential_reflect (j : Fin 3) (u : FiberSpace) :
    potential (fiber j u) = fiber j (potential u) := by
  apply Subtype.ext
  funext ν
  change potential (fiber j u) ν = polarization j (potential u (aliasEquiv j ν))
  rw [potential_apply, potential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, map_add, fiber_apply, fiber_apply, alias_add_unit, alias_sub_unit]
  by_cases hk : k = j
  · simp only [hk, ↓reduceIte]
    exact congrArg (fun v : Polarization => (potentialWeight j : ℂ) • v)
      (add_comm (polarization j (u (aliasEquiv j ν - unitAlias j)))
        (polarization j (u (aliasEquiv j ν + unitAlias j))))
  · simp only [hk, ↓reduceIte]

/-- Exact graph intertwining transfers domain membership as well as the output. -/
theorem free_graph_reflect (j : Fin 3) (q : Momentum) (E : ℂ) (u v : FiberSpace)
    (h : (u, v) ∈ (operator q E).graph) :
    (fiber j u, fiber j v) ∈ (operator (momentum j q) E).graph := by
  apply (operator_graph_iff _ _ _ _).mpr
  intro ν
  rw [aliasMomentum_reflect, fiber_apply, block_reflect]
  exact congrArg (polarization j) ((operator_graph_iff _ _ _ _).mp h (aliasEquiv j ν))

end Maxwell.Continuum.FiberReflection
