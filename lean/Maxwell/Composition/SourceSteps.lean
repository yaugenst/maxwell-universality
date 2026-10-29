import Maxwell.Composition.SourceSubdivision
import Maxwell.Composition.SubdivisionSupport

/-! Chronological unit-edge indices for the actual routed source graph.
The sparse support theorem includes every path endpoint and internal edge. -/
noncomputable section
namespace Maxwell.Composition.SourceSteps
open Maxwell.Logical.Routing
attribute [local instance] Classical.propDecidable

variable (S : Source.SparseSystem) (precision : ℕ)

abbrev Step : Type := SubdivisionSteps.Step (SourceRouting.data S precision)
def left (s : Step S precision) : SourceRouting.Vertex S precision :=
  SubdivisionSteps.left (SourceRouting.data S precision) s
def right (s : Step S precision) : SourceRouting.Vertex S precision :=
  SubdivisionSteps.right (SourceRouting.data S precision) s

theorem distinct (s : Step S precision) : left S precision s ≠ right S precision s := by
  intro he
  change Subdivision.edgeVertex (SourceRouting.data S precision) s.1 s.2.castSucc =
    Subdivision.edgeVertex (SourceRouting.data S precision) s.1 s.2.succ at he
  have ht := Subdivision.edgeVertex_injective (SourceRouting.data S precision) s.1 he
  have hv := congrArg (fun t : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S precision) s.1).length + 1) => t.val) ht
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

theorem matrix_step (s : Step S precision) :
    SourceSubdivision.matrix S precision (left S precision s) (right S precision s) = 1 :=
  SubdivisionSteps.matrix_step (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (fun e => (SourceRouting.data_endpoint S precision e false).symm)
    (fun e => (SourceRouting.data_endpoint S precision e true).symm) (fun _ => rfl) s

theorem matrix_support (a b : SourceRouting.Vertex S precision) (hne : a ≠ b)
    (h : SourceSubdivision.matrix S precision a b ≠ 0) :
    ∃ s : Step S precision, (a = left S precision s ∧ b = right S precision s) ∨
      (a = right S precision s ∧ b = left S precision s) :=
  SubdivisionSteps.matrix_support (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (fun e => (SourceRouting.data_endpoint S precision e false).symm)
    (fun e => (SourceRouting.data_endpoint S precision e true).symm) a b hne h

theorem unordered_injective (a b : Step S precision)
    (h : (left S precision a = left S precision b ∧ right S precision a = right S precision b) ∨
      (left S precision a = right S precision b ∧ right S precision a = left S precision b)) : a = b :=
  SubdivisionSteps.unordered_injective (SourceRouting.data S precision) a b h

end Maxwell.Composition.SourceSteps
