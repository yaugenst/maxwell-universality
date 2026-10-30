import Maxwell.Continuum.SourceRoutingAssemblyGeometry
import Maxwell.Continuum.SourceRoutingTreeChildren

/-! One reverse visit realizes the recursive label equation from actual
stored child labels and colors, with the full private machine execution. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyNode
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem executes (heap rootCount rootWidth node rows columns B : ℕ) (q : ℕ→ℕ)
    (hB : 1 ≤ B) (hn : 2*2^(columns+rows) ≤ rootCount) (hw : columns+rows+2 ≤ rootWidth)
    (hcount : q 801=2*2^(columns+rows))
    (hlayout : Assembly.layout q=layout heap rootCount rootWidth node (columns+rows))
    (hq : ∀i∈Assembly.controls,(q i).bits.length ≤ B)
    (target : Targets.Target rows (columns+1))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : PrivateVisit.Clean s)
    (hi : ∀i∈Assembly.controls,RationalAccumulator.Word s.val i (q i))
    (colors : Outputs.At heap rootCount rootWidth node rows columns target s.val.memory)
    (labels : ∀b,StoredLabels rows columns (ColorData.childTarget rows columns target b) s.val.memory
      (Leaves.labelBase heap rootCount rootWidth (child node b) (2^(columns+rows)) (columns+rows+1))
      (columns+rows+1)) :
    ∃steps t,Executes input tape PrivateAssembly.code steps s t ∧
      steps ≤ 2^45*(q 801+1)*(B+2)^2 ∧
      StoredLabels rows (columns+1) target t.val.memory
        (Leaves.labelBase heap rootCount rootWidth node (2*2^(columns+rows)) (columns+rows+2))
        (columns+rows+2) ∧
      PrivateVisit.Clean t ∧ PrivateNode.Frame s.val t.val ∧
      Memory.Frame (block heap rootCount rootWidth node) (stride rootCount rootWidth) s.val.memory t.val.memory := by
  have width : q 802=columns+rows+2 := congrArg ChildPermutation.Layout.parentWidth hlayout
  have cs : BitArray.Represents s.val.memory (Assembly.layout q).colors 1
      (ColorPass.colorWords (ColorData.assembleData rows columns target).colors) := by
    rw [hlayout]
    have hh:=colors.colors
    rw [ColorAddress.address] at hh
    exact hh
  have ls (b : Bool) := (labels_vector rows columns (ColorData.childTarget rows columns target b)
    s.val.memory _ _).mp (labels b)
  have left : BitArray.Represents s.val.memory (Assembly.layout q).leftForward
      (Assembly.layout q).childWidth
      (DoublingPass.words (Assembly.layout q).childWidth (ColorData.assembleData rows columns target).left) := by
    rw [hlayout]
    simpa only [layout,ChildPermutation.Layout.childWidth,ColorData.assembleData,
      show columns+rows+2-1=columns+rows+1 by omega]
      using ls false
  have right : BitArray.Represents s.val.memory (Assembly.layout q).rightForward
      (Assembly.layout q).childWidth
      (DoublingPass.words (Assembly.layout q).childWidth (ColorData.assembleData rows columns target).right) := by
    rw [hlayout]
    simpa only [layout,ChildPermutation.Layout.childWidth,ColorData.assembleData,
      show columns+rows+2-1=columns+rows+1 by omega]
      using ls true
  obtain ⟨steps,t,he,hcost,rep,zt,ft,mt⟩:=PrivateAssembly.executes q (columns+rows) B hB hcount width hq
    (ColorData.assembleData rows columns target) (by rw [hlayout];exact separated _ _ _ _ _ hn hw)
    input tape s hs hi cs left right
  have result:=assembled_labels rows columns target (Assembly.layout q) t.val.memory rep.output
  rw [hlayout] at result mt
  exact ⟨steps,t,he,hcost,result,zt,ft,memory_frame _ _ _ _ _ hn hw _ _ mt⟩

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyNode
