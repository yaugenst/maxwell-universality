import Maxwell.Continuum.SourceRoutingPathMeaning
import Maxwell.Continuum.SourceRoutingPathThreePhase
import Maxwell.Continuum.SourceRoutingPathReverseThreePhase
import Maxwell.Logical.Routing.SortPathsGeometryReverse

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing
open Maxwell.Composition.SourceDecorationEnumeration (pointWords)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def pointsBits (width : ℕ) (points : List Point) : List Bool :=
  (points.flatMap pointWords).flatMap (IncidenceEncoding.word width)

theorem pointsBits_append (width : ℕ) (xs ys : List Point) :
    pointsBits width (xs++ys)=pointsBits width xs++pointsBits width ys := by
  simp only [pointsBits,List.flatMap_append]

theorem phaseBits_meaning {q : ℕ} (p : GeometryPathPhase.Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) :
    GeometryPathPhase.prefixBits p initial start level cursor transpose k=
      pointsBits p.width (SortPaths.phasePoints initial start level transpose k) := by
  induction k with
  | zero => simp [GeometryPathPhase.prefixBits,SortPaths.phasePoints,pointsBits]
  | succ k ih =>
    rw [GeometryPathPhase.prefixBits,SortPaths.phasePoints_succ,pointsBits_append,ih,
      emittedBits_meaning]
    simp only [Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,pointsBits]

theorem reversePhaseBits_meaning {q : ℕ} (p : GeometryPathPhase.Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) (bound : k ≤ 2*q) :
    GeometryPathReverse.prefixBits p initial start level cursor transpose k=
      pointsBits p.width (SortPaths.reversePhasePoints initial start level transpose (2*q) k) := by
  induction k with
  | zero => simp [GeometryPathReverse.prefixBits,SortPaths.reversePhasePoints,pointsBits]
  | succ k ih =>
    rw [GeometryPathReverse.prefixBits,SortPaths.reversePhasePoints_succ _ _ _ _ _ _ (by omega),
      pointsBits_append,ih (by omega),emittedBits_meaning]
    simp only [Equiv.symm_apply_apply,ite_true,pointsBits]

theorem reversePhaseBits_end {q : ℕ} (p : GeometryPathPhase.Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) :
    GeometryPathReverse.prefixBits p initial start level cursor transpose (2*q)=
      pointsBits p.width ((SortPaths.phasePoints initial start level transpose (2*q)).reverse) := by
  rw [reversePhaseBits_meaning _ _ _ _ _ _ _ le_rfl,SortPaths.reversePhasePoints_end]

#print axioms phaseBits_meaning
#print axioms reversePhaseBits_end
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
