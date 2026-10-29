import Maxwell.Composition.PhysicalSourceBudget

/-! Source amplitude before any spectral event is inspected. This bound
controls emitted bytes even on a singular background draw. -/
noncomputable section
namespace Maxwell.Composition.PhysicalSource
open Maxwell.Composition.PhysicalGram Maxwell.Composition.PhysicalMaterial
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (J : ℕ) (j : Fin J)

theorem backgroundMatrix_norm :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ)
      ((backgroundMatrix P S precision d ζ hζ hζ1 J j).map Rat.cast)‖ ≤ 16 := by
  let M : ScalarMaterial (box P S precision d ζ hζ hζ1).nx
      (box P S precision d ζ hζ hζ1).ny (box P S precision d ζ hζ hζ1).nz :=
    { value := backgroundValue P S precision d ζ hζ hζ1 J j
      bounds := fun c => ⟨(background_bounds P S precision d ζ hζ hζ1 J j c).1, by
        have := (background_bounds P S precision d ζ hζ hζ1 J j c).2
        have := P.background.reserve_pos
        linarith⟩ }
  exact Target.maxwell_real_toEuclideanCLM_norm_le M

theorem unrounded_operator (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g) =
      (α:ℝ) • Matrix.toEuclideanCLM (𝕜:=ℝ)
        ((backgroundMatrix P S precision d ζ hζ hζ1 J j).map Rat.cast)
        (realVector (seed P S precision d ζ hζ hζ1 hd q g)) := by
  ext e
  simp [realVector,unrounded,Matrix.mulVec,dotProduct]

theorem unrounded_norm (α : ℚ) (hα : 0 ≤ α) (q : Local P → ℚ)
    (g : Sites S precision → ℚ) (hq : ‖realVector q‖ ≤ 2) :
    ‖realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g)‖ ≤
      128*(α:ℝ)*‖realVector g‖ := by
  let lay := layout P S precision d ζ hζ hζ1 hd
  have hQ := coordinateExtension_norm_le lay.pick lay.injective
  have hW := lay.inverseWeight_norm_le
  have hseed : ‖realVector (seed P S precision d ζ hζ hζ1 hd q g)‖ ≤ 8*‖realVector g‖ := by
    rw [seed_cast]
    change ‖coordinateExtension lay.pick (lay.inverseWeight (blockInjection (realVector q) (realVector g)))‖ ≤ _
    have hw := (ContinuousLinearMap.le_opNorm lay.inverseWeight
      (blockInjection (realVector q) (realVector g))).trans
      (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
    have he := (ContinuousLinearMap.le_opNorm (coordinateExtension lay.pick)
      (lay.inverseWeight (blockInjection (realVector q) (realVector g)))).trans
      (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    rw [one_mul] at he
    rw [blockInjection_norm_apply] at hw
    have hqg := mul_le_mul_of_nonneg_right hq (norm_nonneg (realVector g))
    nlinarith
  rw [unrounded_operator,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by exact_mod_cast hα)]
  have hK := backgroundMatrix_norm P S precision d ζ hζ hζ1 J j
  have h := (ContinuousLinearMap.le_opNorm
    (Matrix.toEuclideanCLM (𝕜:=ℝ) ((backgroundMatrix P S precision d ζ hζ hζ1 J j).map Rat.cast))
    (realVector (seed P S precision d ζ hζ hζ1 hd q g))).trans
    (mul_le_mul hK hseed (norm_nonneg _) (by norm_num))
  have h' := mul_le_mul_of_nonneg_left h (show (0:ℝ)≤α by exact_mod_cast hα)
  convert h' using 1
  ring

theorem unrounded_coordinate (α : ℚ) (hα : 0 ≤ α) (q : Local P → ℚ)
    (g : Sites S precision → ℚ) (hq : ‖realVector q‖ ≤ 2)
    (e : (box P S precision d ζ hζ hζ1).Edge) :
    |(unrounded P S precision d ζ hζ hζ1 hd J j α q g e:ℝ)| ≤
      128*(α:ℝ)*‖realVector g‖ := by
  exact (PiLp.norm_apply_le (realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g)) e).trans
    (unrounded_norm P S precision d ζ hζ hζ1 hd J j α hα q g hq)

end Maxwell.Composition.PhysicalSource
