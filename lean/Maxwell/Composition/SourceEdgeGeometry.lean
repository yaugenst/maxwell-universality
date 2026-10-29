import Maxwell.Composition.SourceEdgeList
import Maxwell.Composition.SourceDecoration

/-! Arithmetic physical decorations of emitted point pairs. The emitter
computes coordinates and an axis using integer operations, while these
lemmas identify them with the actual physical defect layout. -/
namespace Maxwell.Composition.SourceEdgeList
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice

/-- The unique changed coordinate of an emitted unit edge. -/
def direction (e : Point × Point) : Fin 3 :=
  if e.1.1 ≠ e.2.1 then 0 else if e.1.2.1 ≠ e.2.2.1 then 1 else 2

def shifted (p : Point) : Site := ![p.1 + 4, p.2.1 + 4, p.2.2 + 16]

def terminalPoint (p : Point) : Site := (2 : ℤ) • shifted p

def mediatorPoint (e : Point × Point) : Site := shifted e.1 + shifted e.2

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

theorem shifted_embedding (v : SourceRouting.Vertex S precision) :
    shifted (SourceRouting.embedding S precision v) = SourceIncidence.position S precision v :=
  (SourceIncidence.position_eq S precision v).symm

theorem terminalPoint_eq (v : SourceRouting.Vertex S precision) :
    terminalPoint (SourceRouting.embedding S precision v) = SourceDecoration.site S precision (.inl v) := by
  unfold terminalPoint
  rw [shifted_embedding]
  rfl

theorem mediatorPoint_eq (e : SourceIncidence.E S precision) :
    mediatorPoint (coordinate S precision e) = SourceDecoration.site S precision (.inr e) := by
  change shifted (SourceRouting.embedding S precision e.val.1) +
    shifted (SourceRouting.embedding S precision e.val.2) = _
  rw [shifted_embedding, shifted_embedding]
  rfl

theorem direction_eq (e : SourceIncidence.E S precision) :
    direction (coordinate S precision e) = SourceIncidence.axis S precision e := by
  have hs := SourceIncidence.axis_spec S precision e
  rw [SourceIncidence.position_eq, SourceIncidence.position_eq] at hs
  generalize hk : SourceIncidence.axis S precision e = k at hs ⊢
  fin_cases k
  · have hx := congrFun hs 0
    change (SourceRouting.embedding S precision e.val.2).1 + 4 =
      (SourceRouting.embedding S precision e.val.1).1 + 4 + 1 at hx
    have hn : (SourceRouting.embedding S precision e.val.1).1 ≠
        (SourceRouting.embedding S precision e.val.2).1 := by omega
    change (if (SourceRouting.embedding S precision e.val.1).1 ≠
        (SourceRouting.embedding S precision e.val.2).1 then (0 : Fin 3) else _) = _
    rw [ite_eq_left hn]
    rfl
  · have hx := congrFun hs 0
    have hy := congrFun hs 1
    change (SourceRouting.embedding S precision e.val.2).1 + 4 =
      (SourceRouting.embedding S precision e.val.1).1 + 4 + 0 at hx
    change (SourceRouting.embedding S precision e.val.2).2.1 + 4 =
      (SourceRouting.embedding S precision e.val.1).2.1 + 4 + 1 at hy
    have he : (SourceRouting.embedding S precision e.val.1).1 =
        (SourceRouting.embedding S precision e.val.2).1 := by omega
    have hn : (SourceRouting.embedding S precision e.val.1).2.1 ≠
        (SourceRouting.embedding S precision e.val.2).2.1 := by omega
    change (if (SourceRouting.embedding S precision e.val.1).1 ≠
        (SourceRouting.embedding S precision e.val.2).1 then (0 : Fin 3) else
        if (SourceRouting.embedding S precision e.val.1).2.1 ≠
          (SourceRouting.embedding S precision e.val.2).2.1 then 1 else 2) = _
    rw [ite_eq_right (not_not.mpr he), ite_eq_left hn]
    rfl
  · have hx := congrFun hs 0
    have hy := congrFun hs 1
    change (SourceRouting.embedding S precision e.val.2).1 + 4 =
      (SourceRouting.embedding S precision e.val.1).1 + 4 + 0 at hx
    change (SourceRouting.embedding S precision e.val.2).2.1 + 4 =
      (SourceRouting.embedding S precision e.val.1).2.1 + 4 + 0 at hy
    have hex : (SourceRouting.embedding S precision e.val.1).1 =
        (SourceRouting.embedding S precision e.val.2).1 := by omega
    have hey : (SourceRouting.embedding S precision e.val.1).2.1 =
        (SourceRouting.embedding S precision e.val.2).2.1 := by omega
    change (if (SourceRouting.embedding S precision e.val.1).1 ≠
        (SourceRouting.embedding S precision e.val.2).1 then (0 : Fin 3) else
        if (SourceRouting.embedding S precision e.val.1).2.1 ≠
          (SourceRouting.embedding S precision e.val.2).2.1 then 1 else 2) = _
    rw [ite_eq_right (not_not.mpr hex), ite_eq_right (not_not.mpr hey)]
    rfl

end
end Maxwell.Composition.SourceEdgeList
