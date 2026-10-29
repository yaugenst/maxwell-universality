import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.CalibrationMatrix.Fill
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Blank)

/-- Public graph descriptors are separate from the private initialization banks. -/
structure Ports where
  width : ℕ
  base : ℕ
  clock : ℕ
  count : ℕ
  valid : ∀ i ∈ [width,base,clock,count], 140  ≤  i ∧ i  ≤  154

structure Ready (p : Ports) (width base clock : List Bool) (value : ℕ) (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  seven : Blank s 7
  temporary : Blank s 37
  widthWord : BankArray.Word s p.width width
  baseWord : BankArray.Word s p.base base
  clockWord : BankArray.Word s p.clock clock
  valueWord : RationalAccumulator.Word s 162 value

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ i, i=4 ∨ 10 ≤ i → i ≠ 37 → i ≠ 160 → i ≠ 161 → i ≠ 162 → t.tapes i=s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i=s.registers i

theorem Frame.refl (s : BitRAMState) : Frame s s := by constructor <;> intros <;> rfl

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i a b c d e => (k.tapes i a b c d e).trans (h.tapes i a b c d e),
    fun i a b c d e f g => (k.registers i a b c d e f g).trans (h.registers i a b c d e f g)⟩

theorem Frame.of_bank {bank : ℕ} {s t : BitRAMState} (hb : bank=37 ∨ bank=160 ∨ bank=161 ∨ bank=162)
    (h : BankArray.FrameExcept bank s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i a b c d e => h.2.2.2.1 i a (by omega),h.2.2.2.2⟩

def Outside (base width n : ℕ) (s t : BitRAMState) : Prop :=
  ∀ a, a<base ∨ base+n*width ≤ a → t.memory a=s.memory a

theorem Outside.refl (base width n : ℕ) (s : BitRAMState) : Outside base width n s s := by intro a ha; rfl

theorem Outside.trans {base width n : ℕ} {s t u : BitRAMState}
    (h : Outside base width n s t) (k : Outside base width n t u) : Outside base width n s u :=
  fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_memory {base width n : ℕ} {s t : BitRAMState} (h : t.memory=s.memory) :
    Outside base width n s t := fun _ _ => congrFun h _

def snapshot (memory : ℕ → Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => MemoryWord.readBits memory (base+i.val*width) width

theorem snapshot_represents (memory : ℕ → Bool) (base width n : ℕ) :
    BitArray.Represents memory base width (snapshot memory base width n) := by
  refine ⟨?_,?_⟩
  · intro i
    simp [snapshot,Vector.get,Fin.cast]
  · intro i j hj
    simpa [snapshot,Vector.get,Fin.cast] using (MemoryWord.readBits_getElem memory (base+i.val*width) width j hj).symm

theorem write_cost_le (width index base : List Bool) (value B : ℕ)
    (hw : width.length ≤ B) (hi : index.length ≤ B) (hb : base.length ≤ B)
    (hv : addressValue width ≤ B) :
    BankArray.costCap width index base (FixedWidth.bits (addressValue width) value.bits)+
      100*addressValue width+100+(12*index.length+18)  ≤  20000*(B+2)^2 := by
  simp only [BankArray.costCap,ArrayAccess.costCap,FixedWidth.bits_length]
  calc
    _  ≤  1000*(3*B+5)^2+B*(15*(B+B+B+1+B)+24)+4+40*(5*B+3)+100*B+100+(12*B+18) := by
      gcongr <;> omega
    _  ≤  _ := by nlinarith

end Maxwell.Cost.PositiveGraph.Initialize
