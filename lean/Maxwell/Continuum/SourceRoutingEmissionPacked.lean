import Maxwell.Continuum.SourceRoutingEmissionControls

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

theorem packed_write {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (memory : ℕ→Bool) (base width : ℕ) :
    MemoryWord.writeBits
      (MemoryWord.writeBits memory base (pointsBits width (List.ofFn saved.original.get)))
      (base+3*v*width) (pathRecordsBits saved width e)=
      MemoryWord.writeBits memory base ((packed saved).flatMap (IncidenceEncoding.word width)) := by
  have size : (pointsBits width (List.ofFn saved.original.get)).length=3*v*width:=by
    rw [pointsBits_length,List.length_ofFn]
  rw [←size,writeBits_append]
  congr 1
  simp only [pointsBits,pathRecordsBits,pathRecords,packed,List.flatMap_append,
    List.take_of_length_le (show (List.finRange e).length≤e by simp)]

theorem original_write_pair {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (left : ℕ) (bound : left≤v) (memory : ℕ→Bool) (base width : ℕ) :
    MemoryWord.writeBits
      (MemoryWord.writeBits memory base (pointsBits width (originalPrefix data 0 left)))
      (base+3*left*width) (pointsBits width (originalPrefix data left (v-left)))=
      MemoryWord.writeBits memory base (pointsBits width (List.ofFn (Gluing.vertexPoint data))) := by
  have h:=write_points_append memory base width 0 (originalPrefix data 0 left) (originalPrefix data left (v-left))
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add,originalPrefix_length data 0 left (by omega)] at h
  rw [h,originalPrefix_append,Nat.add_sub_of_le bound,originalPrefix_end]

#print axioms packed_write
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
