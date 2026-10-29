import Maxwell.Continuum.CellBandFourierGauge
import Maxwell.Continuum.CornerBridgeTop

/-! Reversal of all antiperiodic aliases, including the selected corner
state's exact odd parity. This is distinct from coefficient conjugation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberReflection CornerBridge

def reverseAlias : Alias ≃ Alias where
  toFun ν j := -ν j - 1
  invFun ν j := -ν j - 1
  left_inv ν := by funext j; simp
  right_inv ν := by funext j; simp

def reversal : FiberSpace ≃ₗᵢ[ℂ] FiberSpace :=
  ((fiber 0).trans (fiber 1)).trans ((fiber 2).trans (LinearIsometryEquiv.neg ℂ))

theorem reversal_apply (u : FiberSpace) (ν : Alias) : reversal u ν = u (reverseAlias ν) := by
  apply PiLp.ext
  intro j
  change -(polarization 2 (polarization 1 (polarization 0
    (u (aliasEquiv 0 (aliasEquiv 1 (aliasEquiv 2 ν))))))) j = u (reverseAlias ν) j
  have ha : aliasEquiv 0 (aliasEquiv 1 (aliasEquiv 2 ν)) = reverseAlias ν := by
    funext k
    fin_cases k <;> simp [aliasEquiv, reverseAlias]
  rw [ha]
  fin_cases j <;> simp [polarization_apply, coordinateSign]

theorem reversal_involutive (u : FiberSpace) : reversal (reversal u) = u := by
  apply lp.ext
  funext ν
  rw [reversal_apply, reversal_apply]
  exact congrArg (fun a : Alias => u a) (reverseAlias.left_inv ν)

theorem reversal_inner (u v : FiberSpace) : inner ℂ (reversal u) v = inner ℂ u (reversal v) := by
  have h := reversal.inner_map_map u (reversal v)
  rwa [reversal_involutive] at h

theorem reverseAlias_central (ν : Alias) : IsCentralAlias (reverseAlias ν) ↔ IsCentralAlias ν := by
  change (∀ j, -ν j - 1 = -1 ∨ -ν j - 1 = 0) ↔ (∀ j, ν j = -1 ∨ ν j = 0)
  constructor <;> intro h j <;> have hj := h j <;> omega

def reverseParity (s : Corner.Parity) : Corner.Parity := (!s.1, !s.2.1, !s.2.2)

theorem reverseAlias_cubeAlias (s : Corner.Parity) : reverseAlias (cubeAlias s) = cubeAlias (reverseParity s) := by
  obtain ⟨a,b,c⟩ := s
  funext j
  cases a <;> cases b <;> cases c <;> fin_cases j <;>
    norm_num [reverseAlias, alias_apply, parityBoolEquiv, reverseParity]

theorem normalizedCorner_reverse (s : Corner.Parity) :
    Corner.normalizedClusterVector (reverseParity s) = -Corner.normalizedClusterVector s := by
  obtain ⟨a,b,c⟩ := s
  funext j
  cases a <;> cases b <;> cases c <;> fin_cases j <;>
    simp [Corner.normalizedClusterVector, Corner.embedding, Corner.reflect, Corner.character,
      Corner.waveSigns, Corner.selectedParity, Corner.sign, reverseParity]

theorem reversal_topState : reversal topState.val = -topState.val := by
  apply lp.ext
  funext ν
  rw [reversal_apply]
  by_cases hν : IsCentralAlias ν
  · obtain ⟨s, hs⟩ := parityAliasEquiv.surjective ⟨ν,hν⟩
    have hνs : cubeAlias s = ν := congrArg Subtype.val hs
    rw [← hνs, reverseAlias_cubeAlias]
    change packReal Corner.normalizedClusterVector (cubeAlias (reverseParity s)) =
      -(packReal Corner.normalizedClusterVector (cubeAlias s))
    rw [packReal, pack_alias, pack_alias]
    apply PiLp.ext
    intro j
    change ((Corner.normalizedClusterVector (reverseParity s) j : ℝ) : ℂ) =
      -((Corner.normalizedClusterVector s j : ℝ) : ℂ)
    rw [normalizedCorner_reverse]
    simp
  · have hr : ¬IsCentralAlias (reverseAlias ν) := mt (reverseAlias_central ν).mp hν
    change packReal Corner.normalizedClusterVector (reverseAlias ν) =
      -(packReal Corner.normalizedClusterVector ν)
    rw [packReal, pack_noncentral _ _ hr, pack_noncentral _ _ hν, neg_zero]

theorem material_graph_reverse (q : Momentum) (E : ℂ) (ρ : ℝ) (u v : FiberSpace)
    (h : (u,v) ∈ (materialFiber q E ρ).graph) :
    (reversal u, reversal v) ∈ (materialFiber (-q) E ρ).graph := by
  have h0 := material_graph_reflect 0 q E ρ u v h
  have h1 := material_graph_reflect 1 _ E ρ _ _ h0
  have h2 := material_graph_reflect 2 _ E ρ _ _ h1
  rw [PeriodicBand.reflect_all] at h2
  exact (materialFiber (-q) E ρ).graph.neg_mem h2

#print axioms reversal_topState
#print axioms material_graph_reverse

end Maxwell.Continuum.CellBandFourier
