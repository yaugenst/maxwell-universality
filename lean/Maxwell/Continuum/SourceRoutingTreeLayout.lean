import Maxwell.Cost.RoutingAllocator.Layout
import Maxwell.Continuum.SourceRoutingFromSource

/-! A breadth-first binary tree uses disjoint fixed-stride node blocks.
Each node uses only its own smaller split slabs. The address space is
polynomial even when unused gaps between blocks are retained. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def stride (rootCount rootWidth : ℕ) : ℕ := 11*(rootCount*rootWidth)
def block (heap rootCount rootWidth node : ℕ) : ℕ := heap+node*stride rootCount rootWidth
def levelNode (depth : ℕ) (i : Fin (2^depth)) : ℕ := 2^depth-1+i.val
def child (node : ℕ) (right : Bool) : ℕ := 2*node+1+right.toNat

theorem child_level (depth : ℕ) (i : Fin (2^depth)) (right : Bool) :
    child (levelNode depth i) right=2^(depth+1)-1+(2*i.val+right.toNat) := by
  have hp : 0<(2 : ℕ)^depth := by positivity
  simp only [child,levelNode,pow_succ]
  omega

theorem level_range (depth : ℕ) (i : Fin (2^depth)) :
    2^depth-1≤levelNode depth i ∧ levelNode depth i<2^(depth+1)-1 := by
  have hp : 0<(2 : ℕ)^depth := by positivity
  have hi := i.isLt
  simp only [levelNode,pow_succ]
  omega

theorem block_separated (heap rootCount rootWidth a b : ℕ) (hab : a≠b) :
    IncidenceEncoding.Separated (block heap rootCount rootWidth a) (stride rootCount rootWidth)
      (block heap rootCount rootWidth b) (stride rootCount rootWidth) := by
  rcases lt_or_gt_of_ne hab with h|h
  · left
    have hh := Nat.mul_le_mul_right (stride rootCount rootWidth) (show a+1≤b by omega)
    dsimp only [block]
    nlinarith only [hh]
  · right
    have hh := Nat.mul_le_mul_right (stride rootCount rootWidth) (show b+1≤a by omega)
    dsimp only [block]
    nlinarith only [hh]

theorem node_fits (heap rootCount rootWidth node n w : ℕ) (hn : n≤rootCount) (hw : w≤rootWidth) :
    RoutingAllocator.nextFrontier (block heap rootCount rootWidth node) n w≤
      block heap rootCount rootWidth node+stride rootCount rootWidth := by
  have hh := Nat.mul_le_mul hn hw
  dsimp only [RoutingAllocator.nextFrontier,RoutingAllocator.slab,stride]
  omega

theorem slab_fits (heap rootCount rootWidth node n w slot : ℕ)
    (hn : n≤rootCount) (hw : w≤rootWidth) (hslot : slot<11) :
    block heap rootCount rootWidth node≤
      RoutingAllocator.slab (block heap rootCount rootWidth node) n w slot ∧
    RoutingAllocator.slab (block heap rootCount rootWidth node) n w slot+n*w≤
      block heap rootCount rootWidth node+stride rootCount rootWidth :=
  ⟨RoutingAllocator.slab_lower _ _ _ _,
    (RoutingAllocator.slab_upper _ _ _ _ hslot).trans (node_fits _ _ _ _ _ _ hn hw)⟩

theorem slab_separated (heap rootCount rootWidth a b na wa nb wb ia ib : ℕ)
    (hab : a≠b) (hna : na≤rootCount) (hwa : wa≤rootWidth)
    (hnb : nb≤rootCount) (hwb : wb≤rootWidth) (hia : ia<11) (hib : ib<11) :
    IncidenceEncoding.Separated
      (RoutingAllocator.slab (block heap rootCount rootWidth a) na wa ia) (na*wa)
      (RoutingAllocator.slab (block heap rootCount rootWidth b) nb wb ib) (nb*wb) := by
  have ha := slab_fits heap rootCount rootWidth a na wa ia hna hwa hia
  have hb := slab_fits heap rootCount rootWidth b nb wb ib hnb hwb hib
  rcases block_separated heap rootCount rootWidth a b hab with h|h
  · exact Or.inl (ha.2.trans (h.trans hb.1))
  · exact Or.inr (hb.2.trans (h.trans ha.1))

theorem cubic_space (depth : ℕ) :
    (2^(depth+1)-1)*stride (2^(2*depth)) (2*depth+1)≤
      22*(2^depth)^3*(2*depth+1) := by
  have hp : 2^(depth+1)-1≤2*2^depth := by rw [pow_succ]; omega
  have he : (2 : ℕ)^(2*depth)=(2^depth)^2 := by rw [Nat.mul_comm 2 depth,pow_mul]
  have hh := Nat.mul_le_mul_right (stride (2^(2*depth)) (2*depth+1)) hp
  calc
    _ ≤ (2*2^depth)*stride (2^(2*depth)) (2*depth+1) := hh
    _ = _ := by simp only [stride,he]; ring

theorem level_population (total depth : ℕ) (hd : depth≤total) :
    2^depth*2^(total-depth)=2^total := by
  rw [←pow_add,Nat.add_sub_of_le hd]

#print axioms slab_separated
#print axioms cubic_space
#print axioms level_population

end Maxwell.Cost.RoutingPorts.Complete.Tree
