import Maxwell.Continuum.SourceRoutingColorLabels
import Maxwell.Continuum.SourceRoutingTreeLayout

/-! A complete breadth-first family of the deterministic recursive routing
targets. Parent indices and child bits are ordinary quotient and remainder. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Targets
open Maxwell.Logical.Routing Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

abbrev Target (rows columns : ℕ) := Equiv.Perm (Columns columns×Fin (2^rows))

def parent (d : ℕ) (i : Fin (2^(d+1))) : Fin (2^d) :=
  ⟨i.val/2,by
    have hi : i.val<2^d*2 := by simpa only [pow_succ] using i.isLt
    omega⟩

def bit {n : ℕ} (i : Fin n) : Bool := decide (i.val%2=1)

theorem bit_value {n : ℕ} (i : Fin n) : (bit i).toNat=i.val%2 := by
  have h := Nat.mod_lt i.val (by decide : 0<2)
  by_cases hi : i.val%2=1
  · simp [bit,hi]
  · have hz : i.val%2=0 := by omega
    simp [bit,hz]

def child (d : ℕ) (i : Fin (2^d)) (b : Bool) : Fin (2^(d+1)) :=
  ⟨2*i.val+b.toNat,by
    have hi := i.isLt
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [pow_succ]
    omega⟩

theorem parent_child (d : ℕ) (i : Fin (2^d)) (b : Bool) : parent d (child d i b)=i := by
  apply Fin.ext
  dsimp [parent,child]
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem bit_child (d : ℕ) (i : Fin (2^d)) (b : Bool) : bit (child d i b)=b := by
  cases b <;> simp [bit,child,Nat.add_mod]

theorem child_parent (d : ℕ) (i : Fin (2^(d+1))) : child d (parent d i) (bit i)=i := by
  apply Fin.ext
  dsimp only [child,parent]
  rw [bit_value]
  omega

def castTarget (rows : ℕ) {a b : ℕ} (h : a=b) (t : Target rows a) : Target rows b := h ▸ t

def family (rows total : ℕ) (root : Target rows total) :
    (d : ℕ)→Fin (2^d)→Target rows (total-d)
  | 0, _ => castTarget rows (by omega) root
  | d+1, i => if hd : d<total then
      ColorData.childTarget rows (total-(d+1))
        (castTarget rows (by omega) (family rows total root d (parent d i))) (bit i)
    else Equiv.refl _

def atParent (rows total d : ℕ) (root : Target rows total) (hd : d<total)
    (i : Fin (2^d)) : Target rows (total-(d+1)+1) :=
  castTarget rows (by omega) (family rows total root d i)

theorem family_child (rows total d : ℕ) (root : Target rows total) (hd : d<total)
    (i : Fin (2^d)) (b : Bool) :
    family rows total root (d+1) (child d i b)=
      ColorData.childTarget rows (total-(d+1)) (atParent rows total d root hd i) b := by
  simp only [family,hd,dite_true,parent_child,bit_child,atParent]

theorem heap_child (d : ℕ) (i : Fin (2^d)) (b : Bool) :
    levelNode (d+1) (child d i b)=Tree.child (levelNode d i) b := by
  rw [Tree.child_level]
  rfl

#print axioms family_child
#print axioms heap_child
end Maxwell.Cost.RoutingPorts.Complete.Tree.Targets
