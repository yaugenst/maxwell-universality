import Maxwell.Composition.PhysicalInstance
import Maxwell.Composition.PhysicalCoreInverse

/-! Every admissible complex field for the emitted rational instance obeys
the actual bright and routed-target residual estimates on the same event. -/
noncomputable section
namespace Maxwell.Composition.PhysicalResidual
open Maxwell.Composition.PhysicalGram
open Maxwell.Composition.PhysicalMaterial
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)
variable (J : ℕ) (j : Fin J) (hm : 0 < S.nnz)
variable (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
variable (α ε L : ℚ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L)
variable (q : PhysicalSource.Local P → ℚ)
variable (v : SourceDecoration.Vertex S precision → ℚ)
variable (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) (hv0 : ∀ i, v i ≠ 0)
variable (δ : ℚ) (hδ : 0 < δ) (format : Target.FixedPointFormat)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

local notation "I" => PhysicalInstance.target P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q v hv δ hδ format
local notation "lay" => layout P S precision d ζ hζ hζ1 hd
local notation "K" => realBackground P S precision d ζ hζ hζ1 J j hm hj
local notation "M" => PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v
local notation "g" => PhysicalSource.exactLogicalSource S precision
local notation "G" => ‖g‖
local notation "D" => EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P)
local notation "B" => EuclideanSpace ℝ (SourceDecoration.Vertex S precision)
local notation "C" => ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode

theorem source_error (hb : S.source ≠ 0) (hrow : 16 ≤ P.rowBound)
    (hq : ‖PhysicalSource.realVector q - P.weightedMode‖ ≤
      (1/4 : ℝ) * ε / (32768 * P.rowBound * L)) :
    ‖targetRealSource I - localIdealSource K (lay).weightEquiv
      (coordinateExtension (lay).pick) (blockInjection P.mode ((α : ℝ) • g))‖ ≤
        (α : ℝ)*ε*G/(8192*L) :=
  PhysicalSource.emitted_source_error P S precision d ζ hζ hζ1 hd J j hm hj
    α ε L hα hε hL q hb hrow hq

include hm hj in
theorem source_norm (hb : S.source ≠ 0) (hrow : 16 ≤ P.rowBound)
    (hL1 : 1 ≤ L) (hε1 : ε ≤ 1)
    (hq : ‖PhysicalSource.realVector q - P.weightedMode‖ ≤
      (1/4 : ℝ) * ε / (32768 * P.rowBound * L)) :
    ‖targetRealSource I‖ ≤ 4*(α : ℝ)*P.rowBound*G := by
  have herr := source_error P S precision d ζ hζ hζ1 hd J j hm hj α ε L hα hε hL q v hv δ hδ format hb hrow hq
  have heq : localIdealSource K (lay).weightEquiv (coordinateExtension (lay).pick)
      (blockInjection P.mode ((α : ℝ) • g)) =
      (α : ℝ) • localIdealSource K (lay).weightEquiv (coordinateExtension (lay).pick)
        (blockInjection P.mode g) := by simp [localIdealSource]
  rw [heq] at herr
  exact (lay).emitted_source_norm_le K (α : ℝ) (P.rowBound : ℝ) (L : ℝ) (ε : ℝ)
    (by exact_mod_cast hα.le) (by exact_mod_cast (show (1:ℚ) ≤ P.rowBound by linarith))
    (by exact_mod_cast hL1) (by exact_mod_cast hε1)
    ((PhysicalSource.background_norm P S precision d ζ hζ hζ1 J j hm hj).trans (by exact_mod_cast hrow))
    P.mode P.mode_unit g (targetRealSource I) herr

theorem admissible_bright (hb : S.source ≠ 0) (hrow : 16 ≤ P.rowBound)
    (hL1 : 1 ≤ L) (hε1 : ε ≤ 1)
    (hLb : P.constants.backgroundInverseBudget ζ hζ S.nnz
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge) ≤ L)
    (hfloor : P.coreFloor ≤ d) (hzeta : ζ = P.spacing.zeta d)
    (hq : ‖PhysicalSource.realVector q - P.weightedMode‖ ≤
      (1/4 : ℝ) * ε / (32768 * P.rowBound * L))
    (htol : δ ≤ ε/(8192*P.rowBound*2*L))
    (Dc : C ≃L[ℝ] C)
    (hDc : (Dc : C →L[ℝ] C) = (modeComplementProjection P.mode).comp
      ((M).comp (modeComplementInclusion P.mode)))
    (hDi : ‖(Dc.symm : C →L[ℝ] C)‖ ≤ 2/(P.defectGap : ℝ))
    (y : EuclideanSpace ℂ (I).box.Edge) (hy : (I).Admissible y) :
    ‖modeSchur P.mode M Dc (SourcePhysicalDecoder.bright P S precision d ζ hζ hζ1 hd v hv0
      (euclideanRealPart y)) - (α : ℝ) • g‖ ≤ 3*(α : ℝ)*ε*G/4096 := by
  have hcore := PhysicalMaterial.core_binding P S precision d ζ hζ hζ1 hd J j hm hj v hv0
  have hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d := by rw [hzeta]; simp [Realization.SpacingPlatform.zeta]
  have hhalf : (ζ : ℝ) ≤ 1/2 := by
    have h := (P.coreFloor_small d hfloor).1
    rw [hzeta]
    have hR : (P.spacing.zeta d : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr h
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hR
  have hmix : ‖((blockInjection (ι := SourceDecoration.Vertex S precision) P.mode).adjoint.comp
      ((M).comp (modeComplementInclusion P.mode))).comp (Dc.symm : C →L[ℝ] C)‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul (PhysicalCore.bright_complement_bound P S precision d ζ hζ hζ1 hd hm J j hj v hζd hhalf)
      hDi (norm_nonneg (Dc.symm : C →L[ℝ] C)) (by
        have hC : (0:ℝ) ≤ P.greenConstant := by exact_mod_cast P.greenConstant_nonneg
        have hz : (0:ℝ) ≤ ζ := by exact_mod_cast hζ.le
        positivity)).trans
    have hs := PhysicalCoreInverse.mixed_product_small P d hfloor
    simpa only [hzeta, mul_comm] using hs
  have hkinv : ‖((K).symm : EuclideanSpace ℝ (I).box.Edge →L[ℝ] EuclideanSpace ℝ (I).box.Edge)‖ ≤ (L : ℝ) := by
    have hk := PhysicalBackground.real_inverse_bound P _ S.nnz J (width P ζ hζ) hm
      (P.constants.detuningWidth_pos ζ hζ) j hj
    rw [← P.constants.backgroundInverseBudget_cast] at hk
    exact hk.trans (by exact_mod_cast hLb)
  have hsource := source_norm P S precision d ζ hζ hζ1 hd J j hm hj α ε L hα hε hL q v hv δ hδ format
    hb hrow hL1 hε1 hq
  have herr := source_error P S precision d ζ hζ hζ1 hd J j hm hj α ε L hα hε hL q v hv δ hδ format hb hrow hq
  have h := target_admissible_bright_residual_budget I K ((lay).strengthEquiv v hv0) (lay).weightEquiv
    (coordinateRestriction (lay).pick) (coordinateExtension (lay).pick)
    (blockInjection (ι := SourceDecoration.Vertex S precision) P.mode)
    (modeComplementInclusion (ι := SourceDecoration.Vertex S precision) P.mode)
    (blockInjection (ι := SourceDecoration.Vertex S precision) P.mode).adjoint
    (modeComplementProjection (ι := SourceDecoration.Vertex S precision) P.mode) Dc
    (PhysicalInstance.physicalOperator P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q v hv δ hδ format hm hj hv0)
    (coordinateRestriction_extension (lay).pick (lay).injective)
    (modeCoordinate_decomposition P.mode P.mode_unit)
    (by intro c; rw [hcore]; exact (congrArg (fun A : C →L[ℝ] C => A c) hDc).symm)
    (blockInjection_adjoint_cancel P.mode P.mode_unit)
    (modeComplementProjection_injection P.mode P.mode_unit)
    (α : ℝ) (ε : ℝ) G (P.rowBound : ℝ) 2 (L : ℝ)
    (by exact_mod_cast hε.le) (by exact_mod_cast P.rowBound_pos) (by norm_num) (by exact_mod_cast hL)
    hkinv (lay).weightEquiv_norm_le (coordinateRestriction_norm_le (lay).pick (lay).injective)
    (modeAdjoint_norm_le P.mode P.mode_unit) (modeComplementProjection_norm_le P.mode)
    (by rwa [hcore]) g (by convert hsource using 1; ring) herr
    (by exact_mod_cast htol) y hy
  rw [hcore] at h
  exact h

end Maxwell.Composition.PhysicalResidual
