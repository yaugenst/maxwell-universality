import Maxwell.Logical.Routing.EdgeEmission

/-! A single adjacent-pair pass emits the unit edges of a stored path. -/
namespace Maxwell.Logical.Routing.Segments
open EdgeEmission Walk

def ofList {α : Type*} (xs : List α) : List (α × α) := xs.zip xs.tail

@[simp] theorem length {α : Type*} (xs : List α) : (ofList xs).length = xs.length - 1 := by
  simp only [ofList, List.length_zip, List.length_tail]
  omega

theorem of_points {a b : Point} (walk : LatticeWalk a b) :
    ofList (points walk) = List.ofFn (fun t : Fin walk.length =>
      (walk.point t.val, walk.point (t.val + 1))) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [ofList, List.getElem_zip, List.getElem_tail, points,
      List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- Integer height used to orient a unit lattice edge. -/
def height (x : Point) : ℤ := x.1 + x.2.1 + x.2.2

def orient (e : Point × Point) : Point × Point :=
  if height e.1 < height e.2 then e else (e.2, e.1)

theorem orient_eq_or_swap (e : Point × Point) : orient e = e ∨ orient e = (e.2, e.1) := by
  unfold orient
  split <;> simp_all

theorem orient_swap (e : Point × Point) (hne : height e.1 ≠ height e.2) :
    orient (e.2, e.1) = orient e := by
  by_cases h : height e.1 < height e.2
  · simp only [orient, h, show ¬height e.2 < height e.1 by omega, ↓reduceIte]
  · simp only [orient, h, show height e.2 < height e.1 by omega, ↓reduceIte]

end Maxwell.Logical.Routing.Segments
