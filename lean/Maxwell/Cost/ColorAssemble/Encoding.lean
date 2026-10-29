import Maxwell.Cost.ChildPermutation.Common

namespace Maxwell.Cost.ColorAssemble
open ChildPermutation (Layout)

def childIndex (k : ℕ) (i : Fin (2*(2^k))) : Fin (2^k) :=
  ⟨i.val%2^k,Nat.mod_lt _ (by positivity)⟩

structure Data (k : ℕ) where
  colors : Vector Bool (2*(2^k))
  left : Vector (Fin (2^k)) (2^k)
  right : Vector (Fin (2^k)) (2^k)

def Data.child {k : ℕ} (data : Data k) (i : Fin (2*(2^k))) : Fin (2^k) :=
  (if data.colors.get i then data.right else data.left).get (childIndex k i)

def Data.value {k : ℕ} (data : Data k) (i : Fin (2*(2^k))) : Fin (2*(2^k)) :=
  ⟨(data.child i).val+2^k*(data.colors.get i).toNat,by
    have h := (data.child i).isLt
    cases data.colors.get i <;> simp only [Bool.toNat_false,Bool.toNat_true,mul_zero,mul_one,add_zero] <;> omega⟩

def Data.values {k : ℕ} (data : Data k) : Vector (Fin (2*(2^k))) (2*(2^k)) := Vector.ofFn data.value

structure Separated (layout : Layout) (k : ℕ) : Prop where
  colors : IncidenceEncoding.Separated layout.colors (2*(2^k)) layout.parentForward (2*(2^k)*layout.parentWidth)
  left : IncidenceEncoding.Separated layout.leftForward (2^k*layout.childWidth) layout.parentForward (2*(2^k)*layout.parentWidth)
  right : IncidenceEncoding.Separated layout.rightForward (2^k*layout.childWidth) layout.parentForward (2*(2^k)*layout.parentWidth)

abbrev Output (k : ℕ) := Vector (List Bool) (2*(2^k))

structure Represents {k : ℕ} (layout : Layout) (memory : ℕ → Bool) (data : Data k) (out : Output k) : Prop where
  colors : BitArray.Represents memory layout.colors 1 (ColorPass.colorWords data.colors)
  left : BitArray.Represents memory layout.leftForward layout.childWidth (DoublingPass.words layout.childWidth data.left)
  right : BitArray.Represents memory layout.rightForward layout.childWidth (DoublingPass.words layout.childWidth data.right)
  output : BitArray.Represents memory layout.parentForward layout.parentWidth out

def stepOutput {k : ℕ} (layout : Layout) (data : Data k) (i : Fin (2*(2^k))) (out : Output k) : Output k :=
  out.set i (IncidenceEncoding.word layout.parentWidth (data.value i).val)

def stepMemory {k : ℕ} (layout : Layout) (data : Data k) (i : Fin (2*(2^k))) (memory : ℕ → Bool) : ℕ → Bool :=
  MemoryWord.writeBits memory (layout.parentForward+i.val*layout.parentWidth)
    (IncidenceEncoding.word layout.parentWidth (data.value i).val)

theorem represents_step {k : ℕ} {layout : Layout} {memory : ℕ → Bool} {data : Data k} {out : Output k}
    (h : Represents layout memory data out) (hs : Separated layout k) (i : Fin (2*(2^k))) :
    Represents layout (stepMemory layout data i memory) data (stepOutput layout data i out) := by
  refine ⟨?_,?_,?_,h.output.write i _ (by simp)⟩
  · exact IncidenceEncoding.represents_write_disjoint h.colors layout.parentForward layout.parentWidth i _ (by simp)
      (by simpa only [mul_one] using hs.colors)
  · exact IncidenceEncoding.represents_write_disjoint h.left layout.parentForward layout.parentWidth i _ (by simp) hs.left
  · exact IncidenceEncoding.represents_write_disjoint h.right layout.parentForward layout.parentWidth i _ (by simp) hs.right

def MemoryFrame (layout : Layout) (k : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ p, p<layout.parentForward ∨ layout.parentForward+2*(2^k)*layout.parentWidth≤p → after p=before p

theorem MemoryFrame.refl (layout : Layout) (k : ℕ) (memory : ℕ → Bool) : MemoryFrame layout k memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {layout : Layout} {k : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout k a b) (j : MemoryFrame layout k b c) : MemoryFrame layout k a c :=
  fun p hp => (j p hp).trans (h p hp)

theorem stepMemory_frame {k : ℕ} (layout : Layout) (data : Data k) (i : Fin (2*(2^k))) (memory : ℕ → Bool) :
    MemoryFrame layout k memory (stepMemory layout data i memory) := by
  intro p hp
  apply MemoryWord.writeBits_outside
  rcases hp with hp | hp
  · left; omega
  · right
    simp only [IncidenceEncoding.word_length]
    have h := Nat.mul_le_mul_right layout.parentWidth (Nat.succ_le_of_lt i.isLt)
    nlinarith

end Maxwell.Cost.ColorAssemble
