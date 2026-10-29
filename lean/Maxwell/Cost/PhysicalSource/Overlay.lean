import Maxwell.Cost.PhysicalMaterial.Descriptors
import Maxwell.Cost.CalibrationMatrix.Rows

/-! Actual dense source-seed storage. The three arrays contain positive and
negative numerator parts and the denominator, with one direct address per
retained electric edge. Reads and writes execute the charged BitRAM code. -/
namespace Maxwell.Cost.PhysicalSource.Overlay
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

structure Layout (edges : ℕ) where
  width : List Bool
  clock : List Bool
  bases : Fin 3 → List Bool
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width
  separated : ∀ i j, i ≠ j → IncidenceEncoding.Separated
    (addressValue (bases i)) (edges*addressValue width)
    (addressValue (bases j)) (edges*addressValue width)

def baseTape (i : Fin 3) : ℕ := 330+i.val
def valueTape (i : Fin 3) : ℕ := 334+i.val
abbrev Ready := PhysicalMaterial.Descriptors.Ready

structure Stored {edges : ℕ} (l : Layout edges)
    (words : Fin 3 → Vector (List Bool) edges) (s : BitRAMState) : Prop where
  width : BankArray.Word s 300 l.width
  clock : BankArray.Word s 301 l.clock
  bases : ∀ i, BankArray.Word s (baseTape i) (l.bases i)
  arrays : ∀ i, BitArray.Represents s.memory (addressValue (l.bases i))
    (addressValue l.width) (words i)

def Layout.Sized {edges : ℕ} (l : Layout edges) (B : ℕ) : Prop :=
  l.width.length ≤ B ∧ addressValue l.width ≤ B ∧ ∀ i, (l.bases i).length ≤ B

def value {edges : ℕ} (words : Fin 3 → Vector (List Bool) edges) (i : Fin edges) : ℚ :=
  ((addressValue ((words 0).get i) : ℚ) - addressValue ((words 1).get i)) /
    addressValue ((words 2).get i)

def writeCode (port : Fin 3) : Code :=
  BankArray.writeCanonicalCode 300 333 (baseTape port) 301 (valueTape port)

def readCode (port : Fin 3) : Code :=
  BankArray.readCanonicalCode 300 333 (baseTape port) 301 (valueTape port)

private theorem ready_after {s t : BitRAMState} (h : Ready s)
    (hs : BankArray.Scratch t) (h7 : Blank t 7)
    (h4 : t.tapes 4 = s.tapes 4) : Ready t := by
  intro i hi
  obtain ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩ := hs
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact blank_of_eq h4 (h 4 (by decide))
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

/-- One charged write updates precisely the chosen source array slot and
preserves all other source arrays and persistent operand tapes. -/
theorem write {edges : ℕ} (l : Layout edges) (words : Fin 3 → Vector (List Bool) edges)
    (port : Fin 3) (i : Fin edges) (v B : ℕ) (hl : l.Sized B)
    (hfit : v.bits.length ≤ addressValue l.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Ready s.val) (h37 : Blank s.val 37) (hd : Stored l words s.val)
    (hindex : BankArray.Word s.val 333 index) (hv : Word s.val (valueTape port) v) :
    ∃ cost t, cost ≤ 40000*(B+2)^2 ∧ Executes input tape (writeCode port) cost s t ∧
      Ready t.val ∧ Blank t.val 37 ∧
      Stored l (Function.update words port
        ((words port).set i (FixedWidth.bits (addressValue l.width) v.bits))) t.val ∧
      t.val.memory = MemoryWord.writeBits s.val.memory
        (addressValue (l.bases port)+i.val*addressValue l.width)
          (FixedWidth.bits (addressValue l.width) v.bits) ∧
      BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨c,t,hc,he,hm,ha,hr,h7,h37,hf⟩ := BankArray.write_canonical
    300 333 (baseTape port) 301 (valueTape port) (by decide) (by decide)
    (by dsimp [baseTape]; omega) (by decide) (by dsimp [valueTape]; omega)
    (by decide) (by decide) (by dsimp [baseTape]; omega) input tape
    l.width index (l.bases port) l.clock (words port) i v
    l.width_nonempty hi l.clock_length l.width_positive hfit s hs.scratch (hs 7 (by decide)) h37
    hd.width hindex (hd.bases port) hd.clock hv (hd.arrays port)
  have keep (j : ℕ) (hj : 10≤j) (hj37 : j≠37) : t.val.tapes j=s.val.tapes j :=
    hf.2.2.2.1 j (Or.inr hj) hj37
  refine ⟨c,t,?_,he,ready_after hs hr h7 (hf.2.2.2.1 4 (by decide) (by decide)),h37,
    ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) hd.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) hd.clock,
      fun j => BankArray.word_of_eq (keep (baseTape j) (by dsimp [baseTape]; omega)
        (by dsimp [baseTape]; omega)) (hd.bases j),?_⟩,hm,hf⟩
  · calc
      c ≤ 1000*(B+B+B+5)^2 + B*(15*(B+B+B+1+B)+24)+4 +
          40*(B+B+B+B+B+3)+100*B+100 := by
        apply hc.trans
        dsimp [BankArray.costCap,ArrayAccess.costCap]
        rw [FixedWidth.bits_length]
        gcongr <;> first | exact hl.1 | exact hl.2.1 | exact hil | exact hl.2.2 port
      _ ≤ _ := by nlinarith
  · intro j
    by_cases hj : j=port
    · subst j
      simpa only [Function.update_self] using ha
    · rw [Function.update_of_ne hj,hm]
      exact IncidenceEncoding.represents_write_disjoint (hd.arrays j) _ _ i _
        (FixedWidth.bits_length _ _) (l.separated j port hj)

/-- One charged read returns the exact canonical word at the selected edge
without changing the overlay or any other persistent field. -/
theorem read {edges : ℕ} (l : Layout edges) (words : Fin 3 → Vector (List Bool) edges)
    (port : Fin 3) (i : Fin edges) (B : ℕ) (hl : l.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Ready s.val) (hd : Stored l words s.val)
    (hindex : BankArray.Word s.val 333 index) (hout : Blank s.val (valueTape port)) :
    ∃ cost t, cost ≤ 20000*(B+2)^2 ∧ Executes input tape (readCode port) cost s t ∧
      Word t.val (valueTape port) (addressValue ((words port).get i)) ∧
      Ready t.val ∧ Stored l words t.val ∧ t.val.memory=s.val.memory ∧
      BankArray.FrameExcept (valueTape port) s.val t.val := by
  obtain ⟨c,t,hc,he,hw,hr,h7,hm,_hreg,hf⟩ := BankArray.read_canonical
    300 333 (baseTape port) 301 (valueTape port) (by decide) (by decide)
    (by dsimp [baseTape]; omega) (by decide) (by dsimp [valueTape]; omega)
    input tape l.width index (l.bases port) l.clock (words port) i
    l.width_nonempty hi l.clock_length s hs.scratch (hs 7 (by decide)) hout
    hd.width hindex (hd.bases port) hd.clock (hd.arrays port)
  have keep (j : ℕ) (hj : 10≤j) (hjp : j≠valueTape port) : t.val.tapes j=s.val.tapes j :=
    hf.2.2.2.1 j (Or.inr hj) hjp
  refine ⟨c,t,hc.trans (CalibrationMatrix.Affine.read_cost_le _ _ _ _ B
    hl.1 hl.2.1 hil (hl.2.2 port) l.clock_length),he,hw,
    ready_after hs hr h7 (hf.2.2.2.1 4 (by decide) (by dsimp [valueTape]; omega)),
    ⟨BankArray.word_of_eq (keep 300 (by decide) (by dsimp [valueTape]; omega)) hd.width,
      BankArray.word_of_eq (keep 301 (by decide) (by dsimp [valueTape]; omega)) hd.clock,
      fun j => BankArray.word_of_eq (keep (baseTape j) (by dsimp [baseTape]; omega)
        (by have := j.isLt; have := port.isLt; simp only [baseTape,valueTape]; omega)) (hd.bases j),
      fun j => by simpa only [hm] using hd.arrays j⟩,hm,?_⟩
  exact hf

end Maxwell.Cost.PhysicalSource.Overlay
