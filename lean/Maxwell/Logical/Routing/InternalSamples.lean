import Maxwell.Logical.Routing.Segments

/-! Removing the two endpoints of a stored path emits each subdivision
vertex once, including the empty-path convention. -/
namespace Maxwell.Logical.Routing.InternalSamples
open EdgeEmission Walk

def ofList {α : Type*} (xs : List α) : List α := xs.tail.dropLast

@[simp] theorem length {α : Type*} (xs : List α) : (ofList xs).length = xs.length - 2 := by
  simp only [ofList, List.length_dropLast, List.length_tail]
  omega

theorem of_points {a b : Point} (walk : LatticeWalk a b) :
    ofList (points walk) = List.ofFn (fun t : Fin (walk.length - 1) => walk.point (t.val + 1)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [ofList, List.getElem_dropLast, List.getElem_tail, points,
      List.getElem_map, List.getElem_range, List.getElem_ofFn]

end Maxwell.Logical.Routing.InternalSamples
