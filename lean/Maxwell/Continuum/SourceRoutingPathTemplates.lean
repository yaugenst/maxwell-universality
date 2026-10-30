import Maxwell.Continuum.SourceGeometryPacking
import Maxwell.Continuum.SourceRoutingPathMovement

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing
open Maxwell.Composition.SourceDecorationEnumeration (pointWords)
set_option maxRecDepth 200000
set_option maxHeartbeats 2400000

inductive Shape where
  | idle
  | swap (strand : Bool)
  | bottom (part : Bool) (arm : Fin 3)
  | top
  deriving DecidableEq

def Shape.length : Shape→ℕ
  | .idle => 16
  | .swap _ => 40
  | .bottom part arm => Terminals.correctedArmLength part arm
  | .top => 48

def Shape.point : (shape : Shape)→Fin shape.length→Point
  | .idle,t => (0,0,t.val)
  | .swap strand,t => RowLayer.swapSample strand t.val
  | .bottom part arm,t => Terminals.correctedArmPoint part arm t.val
  | .top,t => Terminals.topPoint t.val

theorem Shape.length_bound (shape : Shape) : shape.length ≤ 64 := by
  cases shape with
  | idle => decide
  | swap strand => change 40 ≤ 64;decide
  | bottom part arm => cases part <;> fin_cases arm <;> decide
  | top => decide

theorem Shape.shifted_bounds (shape : Shape) :
    ∀t : Fin shape.length,
      (0 ≤ (shape.point t).1+4 ∧ (shape.point t).1+4 ≤ 64) ∧
      (0 ≤ (shape.point t).2.1+4 ∧ (shape.point t).2.1+4 ≤ 64) ∧
      (0 ≤ (shape.point t).2.2+16 ∧ (shape.point t).2.2+16 ≤ 64) := by
  cases shape with
  | idle => decide
  | swap strand => cases strand <;> decide
  | bottom part arm => cases part <;> fin_cases arm <;> decide
  | top => decide

def Shape.words (shape : Shape) : List ℕ :=
  (List.finRange shape.length).flatMap (fun t => pointWords (shape.point t))

theorem Shape.words_length (shape : Shape) : shape.words.length=3*shape.length := by
  have h:=Maxwell.Composition.SourceDecorationEnumeration.triples_length
    ((List.finRange shape.length).map shape.point)
  simpa only [Shape.words,List.flatMap_map,List.length_map,List.length_finRange] using h

theorem Shape.word_bound (shape : Shape) (n : ℕ) (hn : n∈shape.words) : n ≤ 64 := by
  obtain ⟨t,_,hn⟩:=List.mem_flatMap.mp hn
  have bounds:=shape.shifted_bounds t
  simp only [pointWords,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl <;> omega

theorem pointWords_translate (point : Point) (x y z : ℕ)
    (nonnegative : 0 ≤ point.1+4 ∧ 0 ≤ point.2.1+4 ∧ 0 ≤ point.2.2+16) :
    pointWords (translate (x,y,z) point)=
      [x+(point.1+4).toNat,y+(point.2.1+4).toNat,z+(point.2.2+16).toNat] := by
  simp only [pointWords,translate,List.cons.injEq,and_true]
  omega

theorem Shape.translated_words (shape : Shape) (t : Fin shape.length) (x y z : ℕ) :
    pointWords (translate (x,y,z) (shape.point t))=
      [x+((shape.point t).1+4).toNat,y+((shape.point t).2.1+4).toNat,z+((shape.point t).2.2+16).toNat] :=
  pointWords_translate _ _ _ _ ⟨(shape.shifted_bounds t).1.1,
    (shape.shifted_bounds t).2.1.1,(shape.shifted_bounds t).2.2.1⟩

#print axioms Shape.shifted_bounds
#print axioms Shape.translated_words
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
