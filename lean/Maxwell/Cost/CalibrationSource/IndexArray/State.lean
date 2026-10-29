import Maxwell.Cost.CalibrationSource.IndexWidth
import Maxwell.Cost.CalibrationMatrix.EraseWords
import Maxwell.Cost.BankArray.WriteCanonical

namespace Maxwell.Cost.CalibrationSource.IndexArray
open Structured BankArray
open RationalAccumulator (Blank)
open Defect.FiniteStencil Spectral.Lattice
set_option maxRecDepth 4096

structure Data where
  width : List Bool
  clock : List Bool
  base : List Bool
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width

structure Stored (R0 L d N : ℕ) (c : Data) (s : BitRAMState) : Prop where
  width : Word s 100 c.width
  clock : Word s 101 c.clock
  base : Word s 160 c.base
  degree : Word s 274 N.bits
  spacing : Word s 275 d.bits
  radix : Word s 276 (cubeWidth (radius R0 L d N)).bits

def cleanup : List ℕ := [102,280,281,282,283,284,285]
def work : Finset ℕ := Finset.range 10 ∪ {37} ∪ cleanup.toFinset
def Workspace (s : BitRAMState) : Prop := ∀ i ∈ work, Blank s i

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ work → t.tapes i = s.tapes i

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ => rfl⟩
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Stored.of_tapes {R0 L d N : ℕ} {c : Data} {s t : BitRAMState}
    (h : Stored R0 L d N c s)
    (keep : ∀ i, i = 100 ∨ i = 101 ∨ i = 160 ∨ i = 274 ∨ i = 275 ∨ i = 276 → t.tapes i = s.tapes i) :
    Stored R0 L d N c t :=
  ⟨word_of_eq (keep 100 (by omega)) h.width,word_of_eq (keep 101 (by omega)) h.clock,
    word_of_eq (keep 160 (by omega)) h.base,word_of_eq (keep 274 (by omega)) h.degree,
    word_of_eq (keep 275 (by omega)) h.spacing,word_of_eq (keep 276 (by omega)) h.radix⟩

theorem Frame.stored {R0 L d N : ℕ} {c : Data} {s t : BitRAMState}
    (h : Frame s t) (hs : Stored R0 L d N c s) : Stored R0 L d N c t :=
  hs.of_tapes (fun i hi => h.tapes i (by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

def initial (N d radix i : ℕ) : ℕ :=
  if i=274 then N else if i=275 then d else if i=276 then radix else 0

def Sized (R0 L d N : ℕ) (c : Data) (B : ℕ) : Prop :=
  c.width.length ≤ B ∧ addressValue c.width ≤ B ∧ c.base.length ≤ B ∧
  N.bits.length ≤ B ∧ d.bits.length ≤ B ∧ (cubeWidth (radius R0 L d N)).bits.length ≤ B

theorem initial_width {R0 L d N B : ℕ} {c : Data} (h : Sized R0 L d N c B) :
    ∀ i ∈ indexIds, (initial N d (cubeWidth (radius R0 L d N)) i).bits.length ≤ B := by
  obtain ⟨_,_,_,hN,hd,hr⟩ := h
  intro i hi
  simp only [indexIds,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hN
  · exact hd
  · exact hr
  all_goals change 0 ≤ B; omega

theorem stored_initial {R0 L d N : ℕ} {c : Data} {s : BitRAMState}
    (hs : Stored R0 L d N c s) (hw : Workspace s) :
    NatAssign.Bank indexIds (initial N d (cubeWidth (radius R0 L d N))) s := by
  intro i hi
  simp only [indexIds,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [initial,RationalAccumulator.Word,Word] using hs.degree
  · simpa [initial,RationalAccumulator.Word,Word] using hs.spacing
  · simpa [initial,RationalAccumulator.Word,Word] using hs.radix
  all_goals
    change RationalAccumulator.Word s _ 0
    rw [RationalAccumulator.zero_word_iff_blank]
    exact hw _ (by decide)

theorem Workspace.scratch {s : BitRAMState} (h : Workspace s) : Scratch s :=
  ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 5 (by decide),h 6 (by decide),h 8 (by decide),h 9 (by decide)⟩

def Outside (c : Data) (m : ℕ) (s t : BitRAMState) : Prop :=
  ∀ a, (a < addressValue c.base ∨ addressValue c.base+m*addressValue c.width ≤ a) →
    t.memory a = s.memory a

theorem Outside.refl (c : Data) (m : ℕ) (s : BitRAMState) : Outside c m s s := fun _ _ => rfl

theorem Outside.trans {c : Data} {m : ℕ} {s t u : BitRAMState}
    (h : Outside c m s t) (k : Outside c m t u) : Outside c m s u :=
  fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_write {c : Data} {m : ℕ} {s t : BitRAMState}
    (row : Fin m) (payload : List Bool) (hp : payload.length = addressValue c.width)
    (hm : t.memory = MemoryWord.writeBits s.memory
      (addressValue c.base+row.val*addressValue c.width) payload) : Outside c m s t := by
  intro a ha
  rw [hm]
  apply MemoryWord.writeBits_outside
  rw [hp]
  have hslot := Nat.mul_le_mul_right (addressValue c.width) (show row.val+1 ≤ m by omega)
  rcases ha with ha | ha
  · left; omega
  · right; nlinarith

end Maxwell.Cost.CalibrationSource.IndexArray
