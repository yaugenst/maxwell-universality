import Maxwell.Continuum.SourceRoutingPathTemplates
import Maxwell.Continuum.SourceRoutingPathWords

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing
open Maxwell.Composition.SourceDecorationEnumeration (pointWords)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def orient (transpose : Bool) (p : Point) : Point :=
  if transpose then (p.2.1,p.1,p.2.2) else p

def pointEntries (p : Point) : List Entry :=
  [(0,(p.1+4).toNat),(1,(p.2.1+4).toNat),(2,(p.2.2+16).toNat)]

def Shape.indices (shape : Shape) (backwards : Bool) : List (Fin shape.length) :=
  if backwards then (List.finRange shape.length).reverse else List.finRange shape.length

def Shape.points (shape : Shape) (transpose backwards : Bool) : List Point :=
  (shape.indices backwards).map (fun i => orient transpose (shape.point i))

def Shape.entries (shape : Shape) (transpose backwards : Bool) : List Entry :=
  (shape.points transpose backwards).flatMap pointEntries

theorem Shape.indices_length (shape : Shape) (backwards : Bool) :
    (shape.indices backwards).length=shape.length := by
  cases backwards <;> simp [Shape.indices]

theorem Shape.entries_length (shape : Shape) (transpose backwards : Bool) :
    (shape.entries transpose backwards).length=3*shape.length := by
  have helper : ∀xs : List Point,(xs.flatMap pointEntries).length=3*xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons p ps ih => simp only [List.flatMap_cons,List.length_append,pointEntries,List.length_cons,
        List.length_nil,ih];omega
  rw [Shape.entries,helper,Shape.points,List.length_map,Shape.indices_length]

theorem Shape.oriented_bounds (shape : Shape) (transpose : Bool) (i : Fin shape.length) :
    (0 ≤ (orient transpose (shape.point i)).1+4 ∧ (orient transpose (shape.point i)).1+4 ≤ 64) ∧
      (0 ≤ (orient transpose (shape.point i)).2.1+4 ∧ (orient transpose (shape.point i)).2.1+4 ≤ 64) ∧
      (0 ≤ (orient transpose (shape.point i)).2.2+16 ∧ (orient transpose (shape.point i)).2.2+16 ≤ 64) := by
  have h:=shape.shifted_bounds i
  cases transpose <;> simpa [orient,and_comm,and_left_comm] using h

theorem Shape.entry_bound (shape : Shape) (transpose backwards : Bool) (e : Entry)
    (member : e∈shape.entries transpose backwards) : e.2 ≤ 64 := by
  obtain ⟨p,hp,he⟩:=List.mem_flatMap.mp member
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hp
  have bounds:=shape.oriented_bounds transpose i
  simp only [pointEntries,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> omega

def bankOrigin (v : ℕ→ℕ) : Point :=
  (v (axisBank 0),v (axisBank 1),v (axisBank 2))

theorem pointEntries_values (v : ℕ→ℕ) (p : Point)
    (nonnegative : 0 ≤ p.1+4 ∧ 0 ≤ p.2.1+4 ∧ 0 ≤ p.2.2+16) :
    (pointEntries p).map (entryValue v)=pointWords (translate (bankOrigin v) p) := by
  rw [bankOrigin,pointWords_translate p _ _ _ nonnegative]
  rfl

theorem Shape.entryBits_eq (shape : Shape) (transpose backwards : Bool) (width : ℕ) (v : ℕ→ℕ) :
    entryBits width v (shape.entries transpose backwards)=
      ((shape.points transpose backwards).flatMap (fun p => pointWords (translate (bankOrigin v) p))).flatMap
        (IncidenceEncoding.word width) := by
  simp only [entryBits,Shape.entries,List.flatMap_assoc]
  apply List.flatMap_congr
  intro p hp
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hp
  have h:=shape.oriented_bounds transpose i
  rw [←pointEntries_values v _ ⟨h.1.1,h.2.1.1,h.2.2.1⟩,List.flatMap_map]

#print axioms Shape.entryBits_eq
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
