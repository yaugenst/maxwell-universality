import Maxwell.Continuum.SourceRoutingPathShape
import Maxwell.Continuum.SourceRoutingGeometryControlSyntax

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic

inductive ShapeChoice where
  | shape (value : Shape)
  | positive (source : ℕ) (yes no : ShapeChoice)

def ShapeChoice.depth : ShapeChoice→ℕ
  | .shape _ => 0
  | .positive _ yes no => 1+max yes.depth no.depth

def ShapeChoice.Valid : ShapeChoice→Prop
  | .shape _ => True
  | .positive source yes no => source∈controls ∧ source≠1234 ∧ yes.Valid ∧ no.Valid

def ShapeChoice.evaluate : ShapeChoice→(ℕ→ℕ)→Shape
  | .shape value,_ => value
  | .positive source yes no,v => if 0<v source then yes.evaluate v else no.evaluate v

def ShapeChoice.code (choice : ShapeChoice) (transpose backwards : Bool) : Code :=
  match choice with
  | .shape value => shapeCode value transpose backwards
  | .positive source yes no => .seq (.atom (.readTape source 24 23))
      (.branch 23 (yes.code transpose backwards) (no.code transpose backwards))

def rowChoice : ShapeChoice := .positive 1212
  (.positive 1211 (.shape (.swap false)) (.shape (.swap true))) (.shape .idle)

theorem rowChoice_valid : rowChoice.Valid := by simp [rowChoice,ShapeChoice.Valid,controls]
theorem rowChoice_depth : rowChoice.depth=2 := by decide

#print axioms rowChoice_valid
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
