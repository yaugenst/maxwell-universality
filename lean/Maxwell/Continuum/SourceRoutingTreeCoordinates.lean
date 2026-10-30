import Maxwell.Continuum.SourceRoutingTreeDescriptorPlan
import Maxwell.Continuum.SourceRoutingTreeTargets

/-! The runtime breadth-first address arithmetic selects exactly the
four arrays produced by the corresponding parent split. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Coordinates
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

structure Stored (v : ℕ→ℕ) (heap rootCount rootWidth d n w j : ℕ) : Prop where
  heap : v 806=heap
  stride : v 809=Tree.stride rootCount rootWidth
  count : v 811=n
  width : v 812=w
  first : v 814=2^d-2
  index : v 815=j
  two : v 819=2

theorem child_number (d : ℕ) (i : Fin (2^d)) (b : Bool) :
    2^(d+1)-2+(Targets.child d i b).val=2*levelNode d i+b.toNat := by
  have hp : 0<(2 : ℕ)^d := by positivity
  simp only [Targets.child,levelNode,pow_succ]
  omega

theorem divided_parent (d : ℕ) (i : Fin (2^d)) (b : Bool) :
    (2^(d+1)-2+(Targets.child d i b).val)/2=levelNode d i := by
  rw [child_number]
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem remainder_bit (d : ℕ) (i : Fin (2^d)) (b : Bool) :
    (2^(d+1)-2+(Targets.child d i b).val)%2=b.toNat := by
  rw [child_number]
  cases b <;> simp

theorem heap_eq (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ) (i : Fin (2^d)) (b : Bool)
    (hs : Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val) :
    Descriptor.output v 800=block heap rootCount rootWidth (levelNode (d+1) (Targets.child d i b)) := by
  rw [Descriptor.output_heap,hs.heap,hs.first,hs.index,hs.stride]
  have hp : 2 ≤ (2 : ℕ)^(d+1) := by
    rw [pow_succ]
    have : 0<(2:ℕ)^d := by positivity
    omega
  have he : 2^(d+1)-2+(Targets.child d i b).val+1=levelNode (d+1) (Targets.child d i b) := by
    dsimp only [levelNode]; omega
  rw [he]
  rfl

theorem forward_eq (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ) (i : Fin (2^d)) (b : Bool)
    (hs : Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val) :
    Descriptor.output v 803=RoutingAllocator.slab (block heap rootCount rootWidth (levelNode d i))
      (2*n) (w+1) (6+2*b.toNat) := by
  rw [Descriptor.output_forward v hs.two,hs.heap,hs.first,hs.index,hs.stride,hs.count,hs.width,
    divided_parent,remainder_bit]
  rfl

theorem backward_eq (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ) (i : Fin (2^d)) (b : Bool)
    (hs : Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val) :
    Descriptor.output v 804=RoutingAllocator.slab (block heap rootCount rootWidth (levelNode d i))
      (2*n) (w+1) (7+2*b.toNat) := by
  rw [Descriptor.output_backward v hs.two,hs.heap,hs.first,hs.index,hs.stride,hs.count,hs.width,
    divided_parent,remainder_bit]
  rfl

theorem input_separated (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ) (i : Fin (2^d)) (b : Bool)
    (hs : Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val) :
    IncidenceEncoding.Separated (Descriptor.output v 803) (n*w) (Descriptor.output v 804) (n*w) := by
  rw [forward_eq v heap rootCount rootWidth d n w i b hs,backward_eq v heap rootCount rootWidth d n w i b hs]
  have hb := RoutingAllocator.slab_separated (block heap rootCount rootWidth (levelNode d i))
    (2*n) (w+1) (6+2*b.toNat) (7+2*b.toNat) (by omega)
  have hsize : n*w ≤ (2*n)*(w+1) := Nat.mul_le_mul (by omega) (by omega)
  rcases hb with hb|hb
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem parent_before_child (heap rootCount rootWidth node : ℕ) (b : Bool) :
    block heap rootCount rootWidth node+stride rootCount rootWidth ≤
      block heap rootCount rootWidth (Tree.child node b) := by
  have hi : node+1 ≤ Tree.child node b := by dsimp only [Tree.child];omega
  have hh := Nat.mul_le_mul_right (stride rootCount rootWidth) hi
  dsimp only [block]
  nlinarith only [hh]

theorem inputs_before (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ) (i : Fin (2^d)) (b : Bool)
    (hs : Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val)
    (hn : 2*n ≤ rootCount) (hw : w+1 ≤ rootWidth) :
    Descriptor.output v 803+n*w ≤ Descriptor.output v 800 ∧
      Descriptor.output v 804+n*w ≤ Descriptor.output v 800 := by
  rw [forward_eq v heap rootCount rootWidth d n w i b hs,backward_eq v heap rootCount rootWidth d n w i b hs,
    heap_eq v heap rootCount rootWidth d n w i b hs,Targets.heap_child]
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hsize : n*w ≤ (2*n)*(w+1) := Nat.mul_le_mul (by omega) (by omega)
  have hf := (slab_fits heap rootCount rootWidth (levelNode d i) (2*n) (w+1)
    (6+2*b.toNat) hn hw (by omega)).2
  have hr := (slab_fits heap rootCount rootWidth (levelNode d i) (2*n) (w+1)
    (7+2*b.toNat) hn hw (by omega)).2
  have hp := parent_before_child heap rootCount rootWidth (levelNode d i) b
  constructor <;> omega

#print axioms forward_eq
#print axioms inputs_before
end Maxwell.Cost.RoutingPorts.Complete.Tree.Coordinates
