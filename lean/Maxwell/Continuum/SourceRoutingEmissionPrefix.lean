import Maxwell.Continuum.SourceRoutingEmissionEdge
import Maxwell.Continuum.SourceGeometryOffsets

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def pathRecords {v e : ℕ} (saved : SourceEmission.Geometry v e) (count : ℕ) : List ℕ :=
  ((List.finRange e).take count).flatMap (fun i=>pathWords (saved.paths.get i))
def pathRecordsBits {v e : ℕ} (saved : SourceEmission.Geometry v e) (width count : ℕ) : List Bool :=
  (pathRecords saved count).flatMap (IncidenceEncoding.word width)

theorem flat_words_length (width : ℕ) (xs : List ℕ) :
    (xs.flatMap (IncidenceEncoding.word width)).length=xs.length*width := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.flatMap_cons,List.length_append,IncidenceEncoding.word_length,
      List.length_cons,ih];ring

theorem pathRecordsBits_length {v e : ℕ} (saved : SourceEmission.Geometry v e) (width count : ℕ) :
    (pathRecordsBits saved width count).length=(pathRecords saved count).length*width :=
  flat_words_length _ _

theorem pathRecords_zero {v e : ℕ} (saved : SourceEmission.Geometry v e) (width : ℕ) :
    pathRecordsBits saved width 0=[] := by simp [pathRecordsBits,pathRecords]

theorem pathRecordsBits_succ {v e : ℕ} (saved : SourceEmission.Geometry v e) (width : ℕ) (i : Fin e) :
    pathRecordsBits saved width (i.val+1)=pathRecordsBits saved width i.val++
      packedEdgeBits width (saved.paths.get i) := by
  unfold pathRecordsBits pathRecords
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using i.isLt)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getElem_finRange]
  rfl

theorem pathOffset_le_end {v e : ℕ} (saved : SourceEmission.Geometry v e) (count : ℕ) :
    pathOffset saved count≤packedLength saved := by
  have he:=congrArg (fun xs : List (Fin e)=>(xs.flatMap (fun i=>pathWords (saved.paths.get i))).length)
    (List.take_append_drop count (List.finRange e))
  simp only [List.flatMap_append,List.length_append] at he
  rw [←pathOffset_end]
  unfold pathOffset
  simp only [List.take_of_length_le (show (List.finRange e).length≤e by simp)]
  omega

theorem pathRecordsBits_extend {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (memory : ℕ→Bool) (base width : ℕ) (i : Fin e) :
    MemoryWord.writeBits (MemoryWord.writeBits memory (base+3*v*width) (pathRecordsBits saved width i.val))
      (base+pathOffset saved i.val*width) (packedEdgeBits width (saved.paths.get i))=
      MemoryWord.writeBits memory (base+3*v*width) (pathRecordsBits saved width (i.val+1)) := by
  have address : base+pathOffset saved i.val*width=
      base+3*v*width+(pathRecordsBits saved width i.val).length := by
    rw [pathRecordsBits_length]
    unfold pathOffset pathRecords
    ring
  rw [address,writeBits_append,pathRecordsBits_succ]

#print axioms pathRecordsBits_extend
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
