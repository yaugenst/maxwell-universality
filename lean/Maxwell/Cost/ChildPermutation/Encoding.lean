import Maxwell.Cost.BinarySplit.Correctness
import Maxwell.Cost.IncidenceEncoding
import Maxwell.Cost.WordReduceHalf

/-! Exact stored child permutations and inverse scatter, using the numeric
selection made by the executed split colors. -/
namespace Maxwell.Cost.ChildPermutation
open Maxwell.Logical.Routing
open Coloring.NumericSplit
open IncidenceEncoding (word)

structure Layout where
  parentWidth : ℕ
  parentForward : ℕ
  colors : ℕ
  leftForward : ℕ
  leftBackward : ℕ
  rightForward : ℕ
  rightBackward : ℕ

def Layout.childWidth (l : Layout) : ℕ := l.parentWidth-1

def Layout.outputBase (l : Layout) (s : Fin 4) : ℕ :=
  ![l.leftForward,l.leftBackward,l.rightForward,l.rightBackward] s

structure Layout.Separated (l : Layout) (k : ℕ) : Prop where
  outputs : ∀ a b : Fin 4, a ≠ b → IncidenceEncoding.Separated
    (l.outputBase a) (2^k*l.childWidth) (l.outputBase b) (2^k*l.childWidth)
  parent : ∀ s, IncidenceEncoding.Separated l.parentForward ((2*2^k)*l.parentWidth)
    (l.outputBase s) (2^k*l.childWidth)
  colors : ∀ s, IncidenceEncoding.Separated l.colors (2*2^k)
    (l.outputBase s) (2^k*l.childWidth)

structure Data (k : ℕ) where
  target : Equiv.Perm (Fin (2*2^k))
  colors : Vector Bool (2*2^k)
  left : Equiv.Perm (Fin (2^k))
  right : Equiv.Perm (Fin (2^k))
  left_law : ∀ i, (left i).val = (target (selected colors.get false i)).val % 2^k
  right_law : ∀ i, (right i).val = (target (selected colors.get true i)).val % 2^k

/-- The data consumed by the machine use precisely the already executed
split colors and the same recursive routing child permutations. -/
def Data.ofBinarySplit {C R : Type*} [Fintype C] [Fintype R]
    (k : ℕ) (index : C × R ≃ Fin (2^k)) (target : Equiv.Perm (Coloring.BinaryToken C R)) : Data k where
  target := numericPerm (halfIndex index) target
  colors := BinarySplit.colors k (numericPerm (halfIndex index) target)
  left := numericPerm index (Coloring.reducedTarget target (Coloring.binarySplit (halfIndex index) target) false)
  right := numericPerm index (Coloring.reducedTarget target (Coloring.binarySplit (halfIndex index) target) true)
  left_law i := by
    apply reducedTarget_array index target (Coloring.binarySplit (halfIndex index) target)
    · intro j
      rw [BinarySplit.colors_eq_binarySplit]
      simp [Vector.get, Fin.cast]
    · intro j; rfl
  right_law i := by
    apply reducedTarget_array index target (Coloring.binarySplit (halfIndex index) target)
    · intro j
      rw [BinarySplit.colors_eq_binarySplit]
      simp [Vector.get, Fin.cast]
    · intro j; rfl

abbrev Outputs (k : ℕ) := Fin 4 → Vector (List Bool) (2^k)

/-- Forward writes follow the source order; backward writes scatter to the
corresponding child target index. -/
def Data.writeIndex {k : ℕ} (d : Data k) (s : Fin 4) : Equiv.Perm (Fin (2^k)) :=
  ![Equiv.refl _,d.left,Equiv.refl _,d.right] s

def Data.writeValue {k : ℕ} (d : Data k) (s : Fin 4) : Equiv.Perm (Fin (2^k)) :=
  ![d.left,Equiv.refl _,d.right,Equiv.refl _] s

def Data.finalPerm {k : ℕ} (d : Data k) (s : Fin 4) : Equiv.Perm (Fin (2^k)) :=
  (d.writeIndex s).symm.trans (d.writeValue s)

@[simp] theorem Data.finalPerm_zero {k : ℕ} (d : Data k) : d.finalPerm 0 = d.left := by
  ext i; rfl
@[simp] theorem Data.finalPerm_one {k : ℕ} (d : Data k) : d.finalPerm 1 = d.left.symm := by
  ext i; rfl
@[simp] theorem Data.finalPerm_two {k : ℕ} (d : Data k) : d.finalPerm 2 = d.right := by
  ext i; rfl
@[simp] theorem Data.finalPerm_three {k : ℕ} (d : Data k) : d.finalPerm 3 = d.right.symm := by
  ext i; rfl

structure Represents {k : ℕ} (l : Layout) (memory : ℕ → Bool) (d : Data k) (out : Outputs k) : Prop where
  parent : BitArray.Represents memory l.parentForward l.parentWidth
    (DoublingPass.words l.parentWidth (Vector.ofFn d.target))
  colors : BitArray.Represents memory l.colors 1 (ColorPass.colorWords d.colors)
  outputs : ∀ s, BitArray.Represents memory (l.outputBase s) l.childWidth (out s)

def writeOutput {k : ℕ} (width : ℕ) (d : Data k) (i : Fin (2^k)) (s : Fin 4)
    (out : Outputs k) : Outputs k :=
  Function.update out s ((out s).set (d.writeIndex s i).val
    (word width (d.writeValue s i).val) (d.writeIndex s i).isLt)

def writeMemory {k : ℕ} (l : Layout) (d : Data k) (i : Fin (2^k)) (s : Fin 4)
    (memory : ℕ → Bool) : ℕ → Bool :=
  MemoryWord.writeBits memory (l.outputBase s+(d.writeIndex s i).val*l.childWidth)
    (word l.childWidth (d.writeValue s i).val)

theorem represents_write {k : ℕ} {l : Layout} {memory : ℕ → Bool} {d : Data k} {out : Outputs k}
    (h : Represents l memory d out) (hs : l.Separated k) (i : Fin (2^k)) (s : Fin 4) :
    Represents l (writeMemory l d i s memory) d (writeOutput l.childWidth d i s out) := by
  refine ⟨?_,?_,?_⟩
  · exact IncidenceEncoding.represents_write_disjoint h.parent _ _ _ _
      (IncidenceEncoding.word_length _ _) (hs.parent s)
  · exact IncidenceEncoding.represents_write_disjoint h.colors _ _ _ _
      (IncidenceEncoding.word_length _ _) (by simpa only [Nat.mul_one] using hs.colors s)
  · intro t
    by_cases ht : t=s
    · subst t
      simpa only [writeOutput,writeMemory,Function.update_self] using
        (h.outputs s).write (d.writeIndex s i) (word l.childWidth (d.writeValue s i).val)
          (IncidenceEncoding.word_length _ _)
    · simpa only [writeOutput,writeMemory,Function.update_of_ne ht] using
        IncidenceEncoding.represents_write_disjoint (h.outputs t) (l.outputBase s) l.childWidth
          (d.writeIndex s i) (word l.childWidth (d.writeValue s i).val)
          (IncidenceEncoding.word_length _ _) (hs.outputs t s ht)

def stepOutputs {k : ℕ} (width : ℕ) (d : Data k) (i : Fin (2^k)) (out : Outputs k) : Outputs k :=
  writeOutput width d i 3 (writeOutput width d i 2
    (writeOutput width d i 1 (writeOutput width d i 0 out)))

def stepMemory {k : ℕ} (l : Layout) (d : Data k) (i : Fin (2^k)) (memory : ℕ → Bool) : ℕ → Bool :=
  writeMemory l d i 3 (writeMemory l d i 2 (writeMemory l d i 1 (writeMemory l d i 0 memory)))

theorem represents_step {k : ℕ} {l : Layout} {memory : ℕ → Bool} {d : Data k} {out : Outputs k}
    (h : Represents l memory d out) (hs : l.Separated k) (i : Fin (2^k)) :
    Represents l (stepMemory l d i memory) d (stepOutputs l.childWidth d i out) :=
  represents_write (represents_write (represents_write (represents_write h hs i 0) hs i 1) hs i 2) hs i 3

/-- Every bit outside the four output intervals is unchanged. -/
def MemoryFrame (l : Layout) (k : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ p, (∀ s, p<l.outputBase s ∨ l.outputBase s+2^k*l.childWidth≤p) → after p=before p

theorem MemoryFrame.trans {l : Layout} {k : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame l k a b) (h' : MemoryFrame l k b c) : MemoryFrame l k a c :=
  fun p hp => (h' p hp).trans (h p hp)

theorem writeMemory_frame {k : ℕ} (l : Layout) (d : Data k) (i : Fin (2^k))
    (s : Fin 4) (memory : ℕ → Bool) : MemoryFrame l k memory (writeMemory l d i s memory) := by
  intro p hp
  apply MemoryWord.writeBits_outside
  rcases hp s with hl | hr
  · left; omega
  · right
    rw [IncidenceEncoding.word_length]
    have hi := Nat.mul_le_mul_right l.childWidth (Nat.succ_le_of_lt (d.writeIndex s i).isLt)
    nlinarith

theorem stepMemory_frame {k : ℕ} (l : Layout) (d : Data k) (i : Fin (2^k)) (memory : ℕ → Bool) :
    MemoryFrame l k memory (stepMemory l d i memory) :=
  (((writeMemory_frame l d i 0 memory).trans (writeMemory_frame l d i 1 _)).trans
    (writeMemory_frame l d i 2 _)).trans (writeMemory_frame l d i 3 _)

end Maxwell.Cost.ChildPermutation
