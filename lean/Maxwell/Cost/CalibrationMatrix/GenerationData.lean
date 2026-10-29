import Maxwell.Cost.CalibrationMatrix.GeneratedEntry
import Maxwell.Cost.CalibrationMatrix.GeneratedInputs
import Maxwell.Cost.CalibrationMatrix.GeneratedWrite
import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

structure Data (R : ℕ) where
  width : List Bool
  clock : List Bool
  radix : List Bool
  dimension : List Bool
  positiveBase : List Bool
  negativeBase : List Bool
  width_nonempty : 0 < width.length
  width_two : 2 ≤ addressValue width
  clock_length : clock.length = addressValue width
  radix_value : addressValue radix = cubeWidth R
  dimension_value : addressValue dimension = 3*cubeWidth R^3
  separated : IncidenceEncoding.Separated (addressValue positiveBase)
    ((3*cubeWidth R^3)^2*addressValue width) (addressValue negativeBase)
    ((3*cubeWidth R^3)^2*addressValue width)

structure Stored {R : ℕ} (d : Data R) (index : List Bool) (s : BitRAMState) : Prop where
  width : Word s 100 d.width
  clock : Word s 101 d.clock
  index : Word s 102 index
  positiveBase : Word s 110 d.positiveBase
  negativeBase : Word s 111 d.negativeBase
  radix : Word s 121 d.radix
  dimension : Word s 122 d.dimension
  residue : Word s 127 (R%20).bits
  clock2 : Word s 129 (3 : ℕ).bits
  clock5 : Word s 130 (31 : ℕ).bits
  twenty : Word s 131 (20 : ℕ).bits

def Metadata (i : ℕ) : Prop :=
  i = 100 ∨ i = 101 ∨ i = 102 ∨ i = 110 ∨ i = 111 ∨ i = 121 ∨ i = 122 ∨
  i = 127 ∨ i = 129 ∨ i = 130 ∨ i = 131

theorem Stored.of_tapes {R : ℕ} {d : Data R} {index : List Bool} {s t : BitRAMState}
    (h : Stored d index s) (keep : ∀ i, Metadata i → t.tapes i = s.tapes i) : Stored d index t :=
  ⟨word_of_eq (keep 100 (by simp [Metadata])) h.width,
   word_of_eq (keep 101 (by simp [Metadata])) h.clock,
   word_of_eq (keep 102 (by simp [Metadata])) h.index,
   word_of_eq (keep 110 (by simp [Metadata])) h.positiveBase,
   word_of_eq (keep 111 (by simp [Metadata])) h.negativeBase,
   word_of_eq (keep 121 (by simp [Metadata])) h.radix,
   word_of_eq (keep 122 (by simp [Metadata])) h.dimension,
   word_of_eq (keep 127 (by simp [Metadata])) h.residue,
   word_of_eq (keep 129 (by simp [Metadata])) h.clock2,
   word_of_eq (keep 130 (by simp [Metadata])) h.clock5,
   word_of_eq (keep 131 (by simp [Metadata])) h.twenty⟩

def work : Finset ℕ := GeneratedCoordinates.work ∪ GeneratedCleanup.banks.toFinset ∪
  {30,31,32,33,34,35,36,37,80,81,82,83,84,85,86,90,135}

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

theorem Frame.stored {R : ℕ} {d : Data R} {index : List Bool} {s t : BitRAMState}
    (h : Frame s t) (hs : Stored d index s) : Stored d index t :=
  hs.of_tapes (fun i hi => h.tapes i (by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

def Data.Sized {R : ℕ} (d : Data R) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧ d.radix.length ≤ B ∧
  d.dimension.length ≤ B ∧ d.positiveBase.length ≤ B ∧ d.negativeBase.length ≤ B

theorem workspace_of_write {s t : BitRAMState} (hready : Ready t (dotValues 0 0))
    (h37 : Blank t 37) (hf : RowFrame s t)
    (hblank : ∀ i ∈ work, i ≠ 30 → i ≠ 31 → Blank s i) : Workspace t := by
  intro i hi
  by_cases hlow : i < 10
  · interval_cases i
    · exact hready.2.1.1
    · exact hready.2.1.2.1
    · exact hready.2.1.2.2.1
    · exact hready.2.1.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (hf.2.2.2.1 4 (by simp) (by decide) (by decide) (by decide))
        (hblank 4 (by decide) (by decide) (by decide))
    · exact hready.2.1.2.2.2.2.1
    · exact hready.2.1.2.2.2.2.2.1
    · exact hready.2.2
    · exact hready.2.1.2.2.2.2.2.2.1
    · exact hready.2.1.2.2.2.2.2.2.2
  by_cases h30 : i = 30
  · subst i
    have h := hready.1 30 (by decide) (by decide)
    simpa [dotValues,RationalAccumulator.zero_word_iff_blank] using h
  by_cases h31 : i = 31
  · subst i
    have h := hready.1 31 (by decide) (by decide)
    simpa [dotValues,RationalAccumulator.zero_word_iff_blank] using h
  by_cases htarget : i = 37
  · subst i; exact h37
  exact RationalAccumulator.blank_of_eq (hf.2.2.2.1 i (Or.inr (by omega)) h30 h31 htarget)
    (hblank i hi h30 h31)

end Maxwell.Cost.CalibrationMatrix.Generation
