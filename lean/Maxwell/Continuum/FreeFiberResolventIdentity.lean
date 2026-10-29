import Maxwell.Continuum.FreeFiberEnergyShift

/-! Both resolvent identities on the literal maximal-domain material
fiber. Only the energy changes; actual graph transport supplies the domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FreeFiber

theorem material_resolvent_identity (q : Momentum) (E F : ℂ) (ρ : ℝ)
    (R : SelfAdjointResolvent.BoundedInverse (materialFiber q E ρ))
    (T : SelfAdjointResolvent.BoundedInverse (materialFiber q F ρ)) :
    R.map - T.map = (E - F) • (R.map * T.map) := by
  apply ContinuousLinearMap.ext
  intro f
  have hT : (T.map f, f) ∈ (materialFiber q F ρ).graph := by
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨T.map f, T.mem_domain f⟩, rfl, T.apply_map f⟩
  have hs := material_graph_energy_shift q F E ρ (T.map f) f hT
  rw [LinearPMap.mem_graph_iff] at hs
  obtain ⟨u, hu, hMu⟩ := hs
  have hR := R.map_apply u
  rw [hMu, map_add, map_smul] at hR
  have hu' : u.val = T.map f := hu
  rw [hu'] at hR
  change R.map f - T.map f = (E - F) • R.map (T.map f)
  calc
    _ = R.map f - (R.map f + (F - E) • R.map (T.map f)) :=
      congrArg (fun v : FiberSpace => R.map f - v) hR.symm
    _ = -((F - E) • R.map (T.map f)) := by abel
    _ = _ := by rw [← neg_smul, neg_sub]

theorem material_resolvent_identity_rev (q : Momentum) (E F : ℂ) (ρ : ℝ)
    (R : SelfAdjointResolvent.BoundedInverse (materialFiber q E ρ))
    (T : SelfAdjointResolvent.BoundedInverse (materialFiber q F ρ)) :
    R.map - T.map = (E - F) • (T.map * R.map) := by
  calc
    _ = -(T.map - R.map) := by abel
    _ = -((F - E) • (T.map * R.map)) :=
      congrArg Neg.neg (material_resolvent_identity q F E ρ T R)
    _ = _ := by rw [← neg_smul, neg_sub]

end Maxwell.Continuum.FreeFiber
