import Maxwell.Composition.SourceProfile
import Maxwell.Green.CalibrationIndex

/-! The entire expanded source profile is inside the existing emitted PEC
box and its copies are disjoint. No additional buffer or placement guard is
introduced by the local-profile implementation. -/
noncomputable section
namespace Maxwell.Composition.SourceProfile
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil Maxwell.Composition.PhysicalGram
open FiniteStencil
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000

def radius (P : PhysicalPlatform) : ℕ := SourceDefectLayout.radius P.defect+3
abbrev Index (P : PhysicalPlatform) := Fin (3*cubeWidth (radius P)^3)

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0<ζ) (hζ1 : ζ≤1)

def anchor (i : SourceDecoration.Vertex S precision) : Site :=
  (20:ℤ) • DecoratedDefectLayout.conventionalAnchor S precision P.basis P.defect d
    (P.chosenBuffer S precision d ζ hζ hζ1) i

def latticeKey (ik : SourceDecoration.Vertex S precision × Index P) : Edge :=
  edge (anchor P S precision d ζ hζ hζ1 ik.1) (radixEdge (radius P) ik.2)

theorem expanded_spacing (hd : P.spacing.minimumDistance≤d) :
    2*(radius P+1)<20*d := by
  have h := P.radius_floor.trans hd
  unfold radius
  omega

theorem latticeKey_injective (hd : P.spacing.minimumDistance≤d) :
    Function.Injective (latticeKey P S precision d ζ hζ hζ1) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  have hpos : Function.Injective (DecoratedDefectLayout.position S precision P.basis) :=
    (latticeCell_injective _).comp
      (DecoratedDefectLayout.indices_injective S precision P.basis P.basis_injective)
  have hij : i=j := by
    apply hpos
    funext k
    have h := congrArg (fun e : Edge => e.2 k) he
    have ha := abs_le.mp (radixEdge_bound (radius P) a k)
    have hb := abs_le.mp (radixEdge_bound (radius P) b k)
    have hspacing := expanded_spacing P d hd
    simp only [latticeKey,anchor,edge,DecoratedDefectLayout.conventionalAnchor,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
    apply integer_spacing_unique (20*d) (radius P)
      (DecoratedDefectLayout.position S precision P.basis i k)
      (DecoratedDefectLayout.position S precision P.basis j k)
      ((radixEdge (radius P) a).2 k) ((radixEdge (radius P) b).2 k)
      (by exact_mod_cast hspacing) ⟨ha.1,by omega⟩ ⟨hb.1,by omega⟩
    nlinarith only [h]
  subst j
  exact Prod.ext rfl ((radixEdge_injective (radius P)) ((edge_injective _) he))

theorem latticeKey_inside (ik : SourceDecoration.Vertex S precision × Index P) (k : Direction) :
    0<(latticeKey P S precision d ζ hζ hζ1 ik).2 k ∧
      (latticeKey P S precision d ζ hζ hζ1 ik).2 k <
        (Green.boxSide (box P S precision d ζ hζ hζ1) k:ℤ) := by
  have hp := latticeCell_bounds (DecoratedDefectLayout.baseBox S precision P.basis)
    (DecoratedDefectLayout.indices S precision P.basis ik.1) k
  have he := abs_le.mp (radixEdge_bound (radius P) ik.2 k)
  have hmul0 : 0≤(20*d:ℕ)*(Target.latticeCell
      (DecoratedDefectLayout.indices S precision P.basis ik.1) k) := mul_nonneg (by positivity) hp.1
  have hmul := mul_le_mul_of_nonneg_left hp.2.le (by positivity : (0:ℤ)≤(20*d:ℕ))
  change 0<(latticeKey P S precision d ζ hζ hζ1 ik).2 k ∧
    (latticeKey P S precision d ζ hζ hζ1 ik).2 k <
      (Green.boxSide (bufferedBox (DecoratedDefectLayout.baseBox S precision P.basis)
        (SourceDefectLayout.radius P.defect) (20*d)
        (P.chosenBuffer S precision d ζ hζ hζ1)) k:ℤ)
  simp only [latticeKey,anchor,edge,DecoratedDefectLayout.conventionalAnchor,
    DecoratedDefectLayout.position,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    bufferedBox_side,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,radius] at *
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℤ) (SourceDefectLayout.radius P.defect),
    Nat.cast_nonneg (α:=ℤ) (P.chosenBuffer S precision d ζ hζ hζ1)]

def key (ik : SourceDecoration.Vertex S precision × Index P) :
    (box P S precision d ζ hζ hζ1).Edge :=
  finiteEdge _ (latticeKey P S precision d ζ hζ hζ1 ik)
    (latticeKey_inside P S precision d ζ hζ hζ1 ik)

@[simp] theorem key_lattice (ik : SourceDecoration.Vertex S precision × Index P) :
    Target.latticeEdge _ (key P S precision d ζ hζ hζ1 ik)=
      latticeKey P S precision d ζ hζ hζ1 ik := lattice_finiteEdge _ _ _

theorem key_injective (hd : P.spacing.minimumDistance≤d) :
    Function.Injective (key P S precision d ζ hζ hζ1) := by
  intro i j h
  apply latticeKey_injective P S precision d ζ hζ hζ1 hd
  simpa only [key_lattice] using congrArg (Target.latticeEdge _) h

/-- The local finite profile has no support outside this fixed radix cube. -/
theorem profile_covered (σ : ℚ) (q : PhysicalSource.Local P→ℚ)
    (t : Edge×ℚ) (ht : t∈profile P σ q) : ∃ k : Index P,radixEdge (radius P) k=t.1 := by
  have hs := profile_supported P σ q t ht
  exact radixCubeEmbedding_covers (radius P) t.1 hs

end Maxwell.Composition.SourceProfile
