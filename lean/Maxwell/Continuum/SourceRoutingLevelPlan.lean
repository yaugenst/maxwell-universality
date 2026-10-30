import Maxwell.Continuum.SourceRoutingTreeStepCost
import Maxwell.Continuum.SourceRoutingTreeOutputs

/-! The numerical specification of one routing level. All stored inputs,
array addresses and widths are explicit; the executed body is fixed. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def values (initial : ℕ→ℕ) (i : ℕ) : ℕ→ℕ := (Step.output^[i]) initial

theorem values_next (initial : ℕ→ℕ) (i : ℕ) : Step.output (values initial i)=values initial (i+1) :=
  (Function.iterate_succ_apply' Step.output i initial).symm

structure Plan (k : ℕ) where
  initial : ℕ→ℕ
  nodes : ℕ
  heap : ℕ
  rootCount : ℕ
  rootWidth : ℕ
  first : ℕ
  B : ℕ
  B_lower : 3 ≤ B
  count_fits : 2*2^k ≤ rootCount
  width_fits : k+2 ≤ rootWidth
  data : Fin nodes→ChildPermutation.Data k
  colors : ∀i,(data i).colors=BinarySplit.colors k (data i).target
  count : ∀i,i<nodes → values initial i 811=2*2^k
  width : ∀i,i<nodes → values initial i 812=k+2
  two : ∀i,i<nodes → values initial i 819=2
  zero : ∀i,i<nodes → ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values initial i j=0
  words : ∀i,i<nodes → ∀j∈Division.ids,(values initial i j).bits.length ≤ B
  address : ∀i,i<nodes → Descriptor.output (values initial i) 800=block heap rootCount rootWidth (first+i)
  separated : ∀i,i<nodes → IncidenceEncoding.Separated
    (Descriptor.output (values initial i) 803) ((2*2^k)*(k+2))
    (Descriptor.output (values initial i) 804) ((2*2^k)*(k+2))
  forward_before : ∀i,i<nodes → Descriptor.output (values initial i) 803+(2*2^k)*(k+2) ≤
    block heap rootCount rootWidth first
  backward_before : ∀i,i<nodes → Descriptor.output (values initial i) 804+(2*2^k)*(k+2) ≤
    block heap rootCount rootWidth first

def Plan.layout {k : ℕ} (p : Plan k) (i : Fin p.nodes) : SplitNode.Layout :=
  Node.layout (NodeSetup.descriptor (Descriptor.output (values p.initial i.val)))

theorem Plan.layout_eq {k : ℕ} (p : Plan k) (i : Fin p.nodes) :
    p.layout i=RoutingAllocator.layout (block p.heap p.rootCount p.rootWidth (p.first+i.val))
      (2*2^k) (k+2) (Descriptor.output (values p.initial i.val) 803) (Descriptor.output (values p.initial i.val) 804) := by
  change RoutingAllocator.layout (Descriptor.output (values p.initial i.val) 800)
    (Descriptor.output (values p.initial i.val) 801) (Descriptor.output (values p.initial i.val) 802) _ _=_
  rw [p.address i.val i.isLt,Descriptor.output_count,Descriptor.output_width,p.count i.val i.isLt,p.width i.val i.isLt]
  rfl

def Plan.Inputs {k : ℕ} (p : Plan k) (memory : ℕ→Bool) : Prop := ∀i : Fin p.nodes,
  BitArray.Represents memory (Descriptor.output (values p.initial i.val) 803) (k+2)
    (DoublingPass.words (k+2) (Vector.ofFn (p.data i).target)) ∧
  BitArray.Represents memory (Descriptor.output (values p.initial i.val) 804) (k+2)
    (DoublingPass.words (k+2) (Vector.ofFn (p.data i).target.symm))

def Plan.Done {k : ℕ} (p : Plan k) (count : ℕ) (memory : ℕ→Bool) : Prop :=
  ∀i : Fin p.nodes,i.val<count → Outputs.Stored (p.layout i) k (p.data i) memory

theorem Plan.block_mono {k : ℕ} (p : Plan k) (i : ℕ) :
    block p.heap p.rootCount p.rootWidth p.first ≤ block p.heap p.rootCount p.rootWidth (p.first+i) := by
  dsimp only [block]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

theorem Plan.inputs_preserved {k : ℕ} (p : Plan k) (i : Fin p.nodes)
    (before after : ℕ→Bool)
    (hf : Memory.Frame (block p.heap p.rootCount p.rootWidth (p.first+i.val))
      (stride p.rootCount p.rootWidth) before after) (hs : p.Inputs before) : p.Inputs after := by
  intro j
  exact ⟨hf.represents (Or.inl ((p.forward_before j.val j.isLt).trans (p.block_mono i.val))) (hs j).1,
    hf.represents (Or.inl ((p.backward_before j.val j.isLt).trans (p.block_mono i.val))) (hs j).2⟩

theorem Plan.done_preserved {k : ℕ} (p : Plan k) (i : Fin p.nodes)
    (before after : ℕ→Bool)
    (hf : Memory.Frame (block p.heap p.rootCount p.rootWidth (p.first+i.val))
      (stride p.rootCount p.rootWidth) before after) (hs : p.Done i.val before)
    (hi : Outputs.Stored (p.layout i) k (p.data i) after) : p.Done (i.val+1) after := by
  intro j hj
  by_cases he : j=i
  · subst j; exact hi
  · have hji : j.val < i.val := by
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    have hjold:=hs j hji
    rw [p.layout_eq j] at hjold ⊢
    exact Outputs.preserve p.heap p.rootCount p.rootWidth (p.first+j.val) (p.first+i.val) k _ _
      (by omega) p.count_fits p.width_fits (p.data j) before after hf hjold

#print axioms Plan.inputs_preserved
#print axioms Plan.done_preserved
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
