import Maxwell.Continuum.SourceRoutingPathChoice
import Maxwell.Continuum.SourceRoutingPathPhaseMeaning

/-! Fixed terminal programs use the same finite shape emitter as routing slabs.
Only bottom-arm selection reads data; each branch contains literal coordinates. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
open Maxwell.Composition.SourceDecorationEnumeration (pointWords)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def bottomChoice (part : Bool) : ShapeChoice :=
  .positive 1210 (.shape (.bottom part 2))
    (.positive 1209 (.shape (.bottom part 1)) (.shape (.bottom part 0)))

theorem bottomChoice_valid (part : Bool) : (bottomChoice part).Valid := by
  simp [bottomChoice,ShapeChoice.Valid,controls]

theorem bottomChoice_depth (part : Bool) : (bottomChoice part).depth=2 := rfl

theorem bottomChoice_evaluate (part : Bool) (arm : Fin 3) (v : ℕ→ℕ)
    (horizontal : v 1209=if arm=1 then 1 else 0)
    (vertical : v 1210=if arm=2 then 1 else 0) :
    (bottomChoice part).evaluate v=.bottom part arm := by
  fin_cases arm <;> simp [bottomChoice,ShapeChoice.evaluate,horizontal,vertical]

private theorem finRange_map_values (n : ℕ) (f : ℕ→Point) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range,Fin.val_cast]

theorem shapeBits_meaning (shape : Shape) (width : ℕ) (v : ℕ→ℕ) (backwards : Bool) :
    entryBits width v (shape.entries false backwards)=
      pointsBits width ((shape.points false backwards).map (translate (bankOrigin v))) := by
  rw [Shape.entryBits_eq]
  simp only [pointsBits,List.flatMap_map]

theorem bottomBits_meaning {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (incidence : Gluing.Incidence E) (width : ℕ) (v : ℕ→ℕ)
    (origin : bankOrigin v=Gluing.tileTranslation data (data.endpoint incidence.1 incidence.2))
    (backwards : Bool) :
    entryBits width v ((Shape.bottom (data.part (data.endpoint incidence.1 incidence.2))
      (data.arm incidence.1 incidence.2)).entries false backwards)=
      pointsBits width (if backwards then (EdgeEmission.bottomPrefix data incidence).reverse
        else EdgeEmission.bottomPrefix data incidence) := by
  rw [shapeBits_meaning]
  apply congrArg (pointsBits width)
  have forward : ((Shape.bottom (data.part (data.endpoint incidence.1 incidence.2))
      (data.arm incidence.1 incidence.2)).points false false).map (translate (bankOrigin v))=
      EdgeEmission.bottomPrefix data incidence := by
    simpa only [Shape.points,Shape.indices,Bool.false_eq_true,ite_false,List.map_map,
      orient,Shape.length,Shape.point,Function.comp_def,origin,EdgeEmission.bottomPrefix] using
      finRange_map_values (Terminals.correctedArmLength (data.part (data.endpoint incidence.1 incidence.2))
        (data.arm incidence.1 incidence.2)) (fun t =>
        translate (Gluing.tileTranslation data (data.endpoint incidence.1 incidence.2))
          (Terminals.correctedArmPoint (data.part (data.endpoint incidence.1 incidence.2))
            (data.arm incidence.1 incidence.2) t))
  cases backwards
  · exact forward
  · simpa only [Shape.points,Shape.indices,ite_true,Bool.false_eq_true,ite_false,List.map_reverse]
      using congrArg List.reverse forward

theorem topBits_meaning {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (edge : E) (width : ℕ) (v : ℕ→ℕ)
    (origin : bankOrigin v=((32 : ℤ)*(data.pair edge).1.val,(16 : ℤ)*(data.pair edge).2.val,(96 : ℤ)*(2*half))) :
    entryBits width v (Shape.top.entries false false)=pointsBits width (EdgeEmission.topPrefix data edge) := by
  rw [shapeBits_meaning]
  apply congrArg (pointsBits width)
  simpa only [Shape.points,Shape.indices,Bool.false_eq_true,ite_false,List.map_map,
    orient,Shape.length,Shape.point,Function.comp_def,origin,EdgeEmission.topPrefix] using
    finRange_map_values 48 (fun t =>
      translate ((32 : ℤ)*(data.pair edge).1.val,(16 : ℤ)*(data.pair edge).2.val,(96 : ℤ)*(2*half)) (Terminals.topPoint t))

theorem endpointBits_meaning (width : ℕ) (v : ℕ→ℕ) :
    entryBits width v (Shape.endpoint.entries false false)=pointsBits width [bankOrigin v] := by
  rw [shapeBits_meaning]
  simp [Shape.points,Shape.indices,Shape.length,Shape.point,orient,List.finRange_succ,translate]

theorem vertexBits_meaning {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (vertex : V) (width : ℕ) (v : ℕ→ℕ)
    (origin : bankOrigin v=Gluing.tileTranslation data vertex) :
    entryBits width v ((Shape.vertex (data.part vertex)).entries false false)=
      pointsBits width [Gluing.vertexPoint data vertex] := by
  rw [shapeBits_meaning]
  simp [Shape.points,Shape.indices,Shape.length,Shape.point,orient,List.finRange_succ,origin,Gluing.vertexPoint]

#print axioms bottomBits_meaning
#print axioms topBits_meaning
#print axioms vertexBits_meaning
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
