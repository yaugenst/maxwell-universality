import Maxwell.Composition.PhysicalMaterial
import Maxwell.Composition.PhysicalSourceNorm
import Maxwell.Composition.SourceRounding
import Maxwell.Realization.Precision

/-! The emitted source is obtained by rational stencil evaluation followed
by one common dyadic rounding. The exact finite formula is bound to the
weighted local-mode source before estimating either error. -/
noncomputable section
namespace Maxwell.Composition.PhysicalSource
open Maxwell.Composition.PhysicalGram
open Maxwell.Composition.PhysicalMaterial
open Matrix
open scoped BigOperators
set_option synthInstance.maxSize 1024

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (J : ℕ) (j : Fin J)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

abbrev Local := Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card
abbrev Sites := SourceDecoration.Vertex S precision

def backgroundMatrix : Matrix (box P S precision d ζ hζ hζ1).Edge
    (box P S precision d ζ hζ hζ1).Edge ℚ :=
  Target.operator (box P S precision d ζ hζ hζ1)
    (backgroundValue P S precision d ζ hζ hζ1 J j)

def seed (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    (box P S precision d ζ hζ hζ1).Edge → ℚ := fun e =>
  ∑ ik : Sites S precision × Local P,
    if (layout P S precision d ζ hζ hζ1 hd).pick ik = e then
      ((layout P S precision d ζ hζ hζ1 hd).weight ik)⁻¹ * (q ik.2 * g ik.1)
    else 0

def unrounded (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    (box P S precision d ζ hζ hζ1).Edge → ℚ :=
  fun e => α * (backgroundMatrix P S precision d ζ hζ hζ1 J j *ᵥ
    seed P S precision d ζ hζ hζ1 hd q g) e

def realVector {ι : Type*} [Fintype ι] (f : ι → ℚ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => (f i : ℝ)

theorem seed_cast (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    realVector (seed P S precision d ζ hζ hζ1 hd q g) =
      coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick
        ((layout P S precision d ζ hζ hζ1 hd).inverseWeight
          (blockInjection (realVector q) (realVector g))) := by
  ext e
  rw [coordinateExtension_apply]
  change ((∑ ik : Sites S precision × Local P,
    if (layout P S precision d ζ hζ hζ1 hd).pick ik = e then
      ((layout P S precision d ζ hζ hζ1 hd).weight ik)⁻¹ * (q ik.2 * g ik.1)
    else 0 : ℚ) : ℝ) = ∑ ik,
      if (layout P S precision d ζ hζ hζ1 hd).pick ik = e then
        ((layout P S precision d ζ hζ hζ1 hd).weight ik : ℝ)⁻¹ *
          ((q ik.2 : ℝ) * (g ik.1 : ℝ)) else 0
  push_cast
  apply Finset.sum_congr rfl
  intro ik _
  split_ifs <;> push_cast <;> rfl

theorem unrounded_cast (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
    (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g) =
      modeSource (α : ℝ)
        (realBackground P S precision d ζ hζ hζ1 J j hm hj)
        (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick)
        (layout P S precision d ζ hζ hζ1 hd).inverseWeight (realVector q) (realVector g) := by
  have hK : (realBackground P S precision d ζ hζ hζ1 J j hm hj :
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge →L[ℝ]
        EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((backgroundMatrix P S precision d ζ hζ hζ1 J j).map Rat.cast) := by
    rw [backgroundMatrix, background_matrix]
    rfl
  unfold modeSource
  rw [← seed_cast, hK]
  ext e
  simp [realVector, unrounded, Matrix.mulVec, dotProduct]

def rounded (budget : ℚ) (hbudget : 0 < budget)
    (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    (box P S precision d ζ hζ hζ1).Edge → ℚ := fun e =>
  (Realization.selectedRound budget hbudget
    (unrounded P S precision d ζ hζ hζ1 hd J j α q g e)).value

theorem rounded_coordinate_error (budget : ℚ) (hbudget : 0 < budget)
    (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ)
    (e : (box P S precision d ζ hζ hζ1).Edge) :
    |(rounded P S precision d ζ hζ hζ1 hd J j budget hbudget α q g e : ℝ) -
      (unrounded P S precision d ζ hζ hζ1 hd J j α q g e : ℝ)| ≤ (budget : ℝ)/2 := by
  exact_mod_cast Realization.selectedRound_error budget hbudget
    (unrounded P S precision d ζ hζ hζ1 hd J j α q g e)

theorem rounded_error (budget : ℚ) (hbudget : 0 < budget)
    (α : ℚ) (q : Local P → ℚ) (g : Sites S precision → ℚ) :
    ‖realVector (rounded P S precision d ζ hζ hζ1 hd J j budget hbudget α q g) -
      realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g)‖ ≤
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge : ℝ) * ((budget : ℝ)/2) := by
  simpa only [Finset.card_univ] using supported_euclidean_error_le
    (realVector (rounded P S precision d ζ hζ hζ1 hd J j budget hbudget α q g) -
      realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q g)) Finset.univ
    ((budget : ℝ)/2) (by simp) (fun e _ =>
      rounded_coordinate_error P S precision d ζ hζ hζ1 hd J j budget hbudget α q g e)

end Maxwell.Composition.PhysicalSource
