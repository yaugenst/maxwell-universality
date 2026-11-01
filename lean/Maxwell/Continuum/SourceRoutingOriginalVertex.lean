import Maxwell.Continuum.SourceRoutingTerminalPhysical

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)

def originalCode (part : Bool) : Code := terminalCode true (.shape (.vertex part)) false

theorem original_executes {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round : ℕ) (vertex : V) (part : Bool)
    (correctPart : data.part vertex=part) (cursor width base n : ℕ) (clock : List Bool)
    (positive : 0<width) (clockLength : clock.length=width)
    (coordinateWidth : (1024*(2*half)+1).bits.length ≤ width) (room : cursor+192 ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids
      (GeometrySort.seed p round (finProdFinEquiv (Gluing.tilePort (data.tile vertex) 0)).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata p s.val) (output : OutputMetadata width base clock s.val)
    (cursorWord : Word s.val 1253 cursor) :
    ∃steps t,Executes input tape (originalCode part) steps s t ∧
      steps ≤ 2^142*(terminalBound p round width base n+3)^2 ∧
      NatAssign.Bank ids
        (GeometrySort.seed p round (finProdFinEquiv (Gluing.tilePort (data.tile vertex) 0)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧
      OutputMetadata width base clock t.val ∧ Word t.val 1253 (cursor+3) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (pointsBits width [Gluing.vertexPoint data vertex]) ∧
      ArchiveFrame terminalWork s.val t.val ∧
      Tree.Memory.Frame base (n*width) s.val.memory t.val.memory := by
  obtain ⟨steps,t,he,hc,bt,zt,pt,mt,ot,ct,mem,ft,hm⟩:=terminal_executes p round
    (Gluing.tilePort (data.tile vertex) 0) true (.shape (.vertex part)) (by trivial) (by simp [ShapeChoice.depth]) false
    cursor width base n clock positive clockLength coordinateWidth room input tape s bank ready privateBlank metadata output cursorWord
  refine ⟨steps,t,he,hc,bt,zt,pt,mt,ot,by simpa only [ShapeChoice.evaluate,Shape.length] using ct,?_,ft,hm⟩
  rw [ShapeChoice.evaluate] at mem
  have shape := vertexBits_meaning data vertex width
    (terminalValues p round (Gluing.tilePort (data.tile vertex) 0) cursor true)
    (bottom_origin p round (data.tile vertex) 0 cursor)
  rw [correctPart] at shape
  rw [shape] at mem
  exact mem

#print axioms original_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
