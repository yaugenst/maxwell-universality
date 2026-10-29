import Maxwell.Composition.PhysicalSourceBudget
import Maxwell.Composition.SourcePhysicalDecoder
import Maxwell.Composition.TargetRecovery

/-! The literal finite target: every cell, source word, residual tolerance,
and original-input decoder stencil is given by the construction formulas.
It exists on every detuning draw, before the spectral event is considered. -/
noncomputable section
namespace Maxwell.Composition.PhysicalInstance
open Maxwell.Composition.PhysicalGram
set_option synthInstance.maxSize 1024

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)
variable (J : ℕ) (j : Fin J)
variable (α ε L : ℚ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L)
variable (q : PhysicalSource.Local P → ℚ)
variable (v : SourceDecoration.Vertex S precision → ℚ)
variable (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound)
variable (δ : ℚ) (hδ : 0 < δ) (format : Target.FixedPointFormat)

abbrev target : Target.Instance S.n where
  box := box P S precision d ζ hζ hζ1
  material := PhysicalMaterial.material P S precision d ζ hζ hζ1 hd J j v hv
  source := PhysicalSource.emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q
  tolerance := δ
  tolerance_pos := hδ
  decoder := SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd q v format

@[simp] theorem realMatrix :
    (target P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q v hv δ hδ format).realMatrix =
      PhysicalMaterial.matrix P S precision d ζ hζ hζ1 hd J j v hv := rfl

@[simp] theorem realSource :
    targetRealSource (target P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q v hv δ hδ format) =
      PhysicalSource.realVector
        (PhysicalSource.emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q) := rfl

theorem physicalOperator (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) (hv0 : ∀ i, v i ≠ 0) :
    (target P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q v hv δ hδ format).realOperator =
      finitePhysicalOperator (PhysicalMaterial.realBackground P S precision d ζ hζ hζ1 J j hm hj)
        ((layout P S precision d ζ hζ hζ1 hd).strengthEquiv v hv0)
        (coordinateRestriction (layout P S precision d ζ hζ hζ1 hd).pick)
        (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick) :=
  PhysicalMaterial.operator_factorization P S precision d ζ hζ hζ1 hd J j hm hj v hv hv0

end Maxwell.Composition.PhysicalInstance
