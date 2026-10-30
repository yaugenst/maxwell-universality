import Maxwell.Continuum.CalibrationCentral
import Maxwell.Continuum.CornerBridgeCoordinates

/-! Literal orthonormal 24-coordinate representation of the calibration
central space, with the computable eight-sign-cube alias indexing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber ClusterComplement
open scoped InnerProductSpace

abbrev CentralIndex := Corner.Parity × Fin 3
abbrev CentralCoordinates := EuclideanSpace ℂ CentralIndex

def centralCoordinatePack (x : CentralCoordinates) : FiberSpace :=
  CornerBridge.pack (fun s j => x (s,j))

theorem centralCoordinatePack_inner (x y : CentralCoordinates) :
    inner ℂ (centralCoordinatePack x) (centralCoordinatePack y) = inner ℂ x y := by
  rw [centralCoordinatePack, centralCoordinatePack, CornerBridge.pack_inner]
  simp only [PiLp.inner_apply, momentumVector]
  exact (Fintype.sum_prod_type (fun i : CentralIndex => inner ℂ (x i) (y i))).symm

theorem centralCoordinatePack_norm (x : CentralCoordinates) : ‖centralCoordinatePack x‖ = ‖x‖ := by
  have h := centralCoordinatePack_inner x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hs : ‖centralCoordinatePack x‖^2 = ‖x‖^2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem centralCoordinatePack_mem (x : CentralCoordinates) : centralCoordinatePack x ∈ centralSpace := by
  apply (mem_centralSpace_iff _).mpr
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  by_cases hν : IsCentralAlias ν
  · simp only [hν, ↓reduceIte]
  · simp only [hν, ↓reduceIte]
    exact (CornerBridge.pack_noncentral _ ν hν).symm

set_option backward.isDefEq.respectTransparency false in
def centralCoordinateIsometry : CentralCoordinates →ₗᵢ[ℂ] centralSpace where
  toFun x := ⟨centralCoordinatePack x, centralCoordinatePack_mem x⟩
  map_add' x y := by
    apply Subtype.ext
    change centralCoordinatePack (x+y) = centralCoordinatePack x+centralCoordinatePack y
    unfold centralCoordinatePack
    convert! CornerBridge.pack_add (fun s j => x (s,j)) (fun s j => y (s,j)) using 1
  map_smul' c x := by
    apply Subtype.ext
    change centralCoordinatePack (c • x) = c • centralCoordinatePack x
    unfold centralCoordinatePack
    convert! CornerBridge.pack_smul c (fun s j => x (s,j)) using 1
  norm_map' := centralCoordinatePack_norm

theorem centralCoordinateIsometry_surjective : Function.Surjective centralCoordinateIsometry := by
  intro u
  let x : CentralCoordinates := WithLp.toLp 2 (fun i => u.val (CornerBridge.cubeAlias i.1) i.2)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply CornerBridge.eq_of_aliases
  · intro ν hν
    change centralCoordinatePack x ν = 0
    exact CornerBridge.pack_noncentral (fun s j => x (s,j)) ν hν
  · exact centralSpace_noncentral u
  · intro s
    change CornerBridge.pack (fun s j => x (s,j)) (CornerBridge.cubeAlias s) = _
    rw [CornerBridge.pack_alias]
    rfl

def centralUnitary : CentralCoordinates ≃ₗᵢ[ℂ] centralSpace :=
  LinearIsometryEquiv.ofSurjective centralCoordinateIsometry centralCoordinateIsometry_surjective

theorem centralUnitary_apply (x : CentralCoordinates) (s : Corner.Parity) (j : Fin 3) :
    (centralUnitary x).val (CornerBridge.cubeAlias s) j = x (s,j) := by
  change CornerBridge.pack (fun s j => x (s,j)) (CornerBridge.cubeAlias s) j = _
  rw [CornerBridge.pack_alias]
  rfl

theorem centralUnitary_symm_apply (u : centralSpace) (i : CentralIndex) :
    centralUnitary.symm u i = u.val (CornerBridge.cubeAlias i.1) i.2 := by
  have h := centralUnitary_apply (centralUnitary.symm u) i.1 i.2
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

def centralOperatorCoordinates (A : centralSpace →L[ℂ] centralSpace) :
    CentralCoordinates →L[ℂ] CentralCoordinates :=
  centralUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    (A.comp centralUnitary.toLinearIsometry.toContinuousLinearMap)

theorem centralOperatorCoordinates_norm (A : centralSpace →L[ℂ] centralSpace) :
    ‖centralOperatorCoordinates A‖ = ‖A‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound (centralOperatorCoordinates A) (norm_nonneg A) ?_
    intro x
    change ‖centralUnitary.symm (A (centralUnitary x))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (A.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])
  · refine ContinuousLinearMap.opNorm_le_bound A (norm_nonneg (centralOperatorCoordinates A)) ?_
    intro u
    have h := (centralOperatorCoordinates A).le_opNorm (centralUnitary.symm u)
    change ‖centralUnitary.symm (A (centralUnitary (centralUnitary.symm u)))‖ ≤ _ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using h

theorem centralOperatorCoordinates_sub (A B : centralSpace →L[ℂ] centralSpace) :
    centralOperatorCoordinates (A-B) = centralOperatorCoordinates A-centralOperatorCoordinates B := by
  apply ContinuousLinearMap.ext
  intro x
  change centralUnitary.symm ((A-B) (centralUnitary x)) =
    centralUnitary.symm (A (centralUnitary x))-centralUnitary.symm (B (centralUnitary x))
  exact map_sub _ _ _

theorem centralIndex_card : Fintype.card CentralIndex = 24 := by decide

#print axioms centralUnitary
#print axioms centralOperatorCoordinates_norm

end Maxwell.Continuum.Calibration
