import Maxwell.Composition.PhysicalMaterial
import Maxwell.Cost.PhysicalMaterial.Lookup

/-! A fixed rational table gives the background edge mass from the same
stored interior-edge coordinates used by the source serializer. One table
lookup replaces four cell lookups; the common scalar detuning is added once. -/
noncomputable section
namespace Maxwell.Composition.SourceMassTable
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Composition.PhysicalGram
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

def edgeTable (P : PeriodicScalarBackground) (a : Direction) (c : Cell20) : ℚ :=
  let transverse := PeriodicYee.transverseDirections a
  (P.material c + P.material (c-PeriodicYee.unitCell transverse.1) +
    P.material (c-PeriodicYee.unitCell transverse.2) +
    P.material (c-PeriodicYee.unitCell transverse.1-PeriodicYee.unitCell transverse.2))/4

def table (P : PeriodicScalarBackground) (a : Direction) (c : Cell20) : ℚ :=
  let transverse := PeriodicYee.transverseDirections a
  edgeTable P a (c+PeriodicYee.unitCell transverse.1+PeriodicYee.unitCell transverse.2)

theorem edgeTable_cast (P : PeriodicScalarBackground) (a : Direction) (c : Cell20) :
    (edgeTable P a c:ℝ)=P.edgeMaterial (a,c) := by
  simp only [edgeTable,PeriodicScalarBackground.edgeMaterial,PeriodicYee.edgeAverage,
    Rat.cast_div,Rat.cast_add,Rat.cast_ofNat]

/-- Positivity is inherited from the actual four scalar-cell values. -/
theorem table_nonneg (P : PeriodicScalarBackground) (a : Direction) (c : Cell20) :
    0≤table P a c := by
  unfold table edgeTable
  have h1 := (P.bounds (c+PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1+
    PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)).1
  have h2 := (P.bounds ((c+PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1+
    PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)-
      PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1)).1
  have h3 := (P.bounds ((c+PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1+
    PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)-
      PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)).1
  have h4 := (P.bounds ((c+PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1+
    PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)-
      PeriodicYee.unitCell (PeriodicYee.transverseDirections a).1-
      PeriodicYee.unitCell (PeriodicYee.transverseDirections a).2)).1
  dsimp only
  linarith

def orientation {B : Target.Box} : B.Edge→Direction
  | .inl _ => 0 | .inr (.inl _) => 1 | .inr (.inr _) => 2

def coordinates {B : Target.Box} : B.Edge→Cell20
  | .inl (i,j,k) => ![(i.val:ZMod 20),(j.val:ZMod 20),(k.val:ZMod 20)]
  | .inr (.inl (i,j,k)) => ![(i.val:ZMod 20),(j.val:ZMod 20),(k.val:ZMod 20)]
  | .inr (.inr (i,j,k)) => ![(i.val:ZMod 20),(j.val:ZMod 20),(k.val:ZMod 20)]

theorem table_cast (P : PeriodicScalarBackground) {B : Target.Box} (e : B.Edge) :
    (table P (orientation e) (coordinates e):ℝ)=
      periodicCoefficient P.edgeMaterial (Target.latticeEdge B e) := by
  rw [table,edgeTable_cast]
  apply congrArg P.edgeMaterial
  rcases e with (⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)) <;>
    apply Prod.ext <;> first | rfl | (ext a; fin_cases a <;>
      simp [orientation,coordinates,Target.latticeEdge_x,Target.latticeEdge_y,
        Target.latticeEdge_z,edgeMod20,siteMod20,
        PeriodicYee.transverseDirections,PeriodicYee.unitCell,Matrix.vecHead,Matrix.vecTail])

theorem base_average (P : PhysicalPlatform) (B : Target.Box) (e : B.Edge) :
    edgeAverage (PhysicalBackground.material P B).value e =
      table P.background (orientation e) (coordinates e) := by
  have h := Target.latticeEdgeAverage_restriction (PhysicalBackground.material P B)
    P.background.scalar (fun _ => rfl) e
  rw [P.background.lattice_average,←table_cast] at h
  exact_mod_cast h.symm

/-- Exact average of the actual finite background on every detuning draw. -/
theorem background_average (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
    (ζ : ℚ) (hζ : 0<ζ) (hζ1 : ζ≤1) (J : ℕ) (j : Fin J)
    (e : (box P S precision d ζ hζ hζ1).Edge) :
    edgeAverage (PhysicalMaterial.backgroundValue P S precision d ζ hζ hζ1 J j) e =
      table P.background (orientation e) (coordinates e)+64*PhysicalMaterial.sigma P ζ hζ J j := by
  unfold PhysicalMaterial.backgroundValue
  rw [edgeAverage_uniform_shift,base_average]

end Maxwell.Composition.SourceMassTable
