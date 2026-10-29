import Maxwell.Cost.CalibrationSource.RepackLoad
import Maxwell.Cost.CalibrationMatrix.MemoryFrame
import Maxwell.Cost.CalibrationMatrix.GenerationPrefix
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

structure Data where
  width : List Bool
  clock : List Bool
  bases : Fin 2 → List Bool
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width

def Data.output (c : Data) : OutputLayout := ⟨c.bases 0,c.bases 1⟩

def Data.Sized (c : Data) (B : ℕ) : Prop :=
  c.width.length ≤ B ∧ addressValue c.width ≤ B ∧ ∀ a, (c.bases a).length ≤ B

def Data.Separated {m : ℕ} (c : Data) (d : ModeRead.Data m) : Prop :=
  c.output.Separated m (addressValue c.width) ∧ ∀ a b,
    IncidenceEncoding.Separated (addressValue (d.bases a)) (m*addressValue d.width)
      (addressValue (c.bases b)) (m*addressValue c.width)

structure Stored {m : ℕ} (c : Data) (out : Fin 2 → Vector (List Bool) m) (s : BitRAMState) : Prop where
  width : BankArray.Word s 100 c.width
  clock : BankArray.Word s 101 c.clock
  bases : ∀ a : Fin 2, BankArray.Word s (161+a.val) (c.bases a)
  arrays : ∀ a, BitArray.Represents s.memory (addressValue (c.bases a)) (addressValue c.width) (out a)

def Workspace (s : BitRAMState) : Prop :=
  Ready s (dotValues 0 0) ∧ Blank s 4 ∧ Blank s 37 ∧ Blank s 104

theorem Workspace.of_tapes {s t : BitRAMState} (h : Workspace s)
    (same : ∀ j, j < 10 ∨ 30 ≤ j ∧ j ≤ 37 ∨ j = 104 → t.tapes j = s.tapes j) :
    Workspace t := by
  rcases h with ⟨hr,h4,h37,h104⟩
  refine ⟨⟨?_,?_,RationalAccumulator.blank_of_eq (same 7 (by omega)) hr.2.2⟩,
    RationalAccumulator.blank_of_eq (same 4 (by omega)) h4,
    RationalAccumulator.blank_of_eq (same 37 (by omega)) h37,
    RationalAccumulator.blank_of_eq (same 104 (by omega)) h104⟩
  · intro j hj hj'
    exact RationalAccumulator.word_of_eq (same j (by omega)) (hr.1 j hj hj')
  · rcases hr.2.1 with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (same 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (same 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (same 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (same 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (same 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (same 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (same 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (same 9 (by omega)) h9⟩

theorem Stored.of_frame {m : ℕ} {c : Data} {out : Fin 2 → Vector (List Bool) m} {s t : BitRAMState}
    (h : Stored c out s) (hf : Frame s t) (hm : t.memory = s.memory) : Stored c out t := by
  refine ⟨BankArray.word_of_eq (hf.tapes 100 (by omega) (by omega) (by omega) (by omega) (by omega)) h.width,
    BankArray.word_of_eq (hf.tapes 101 (by omega) (by omega) (by omega) (by omega) (by omega)) h.clock,?_,?_⟩
  · intro a
    exact BankArray.word_of_eq (hf.tapes _ (by omega) (by omega) (by omega) (by omega) (by omega)) (h.bases a)
  · intro a; simpa only [hm] using h.arrays a

theorem modeStored_of_frame {m : ℕ} {d : ModeRead.Data m} {s t : BitRAMState}
    (h : ModeRead.Stored readLayout d s) (hf : Frame s t) (hm : t.memory = s.memory) :
    ModeRead.Stored readLayout d t := by
  have keep (j : ℕ) (hj : 510 ≤ j) := hf.tapes j (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨BankArray.word_of_eq (keep 514 (by omega)) h.width,
    BankArray.word_of_eq (keep 515 (by omega)) h.clock,?_,
    RationalAccumulator.word_of_eq (keep 512 (by omega)) h.denominator,?_⟩
  · intro a; apply BankArray.word_of_eq (keep _ _) (h.bases a)
    fin_cases a <;> decide
  · intro a; simpa only [hm] using h.arrays a

theorem Frame.of_literal {s t : BitRAMState} (h : BinaryPrecision.Frame {104} s t) : Frame s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun j _ _ _ _ h104 => h.tapes j (by simpa using h104)⟩

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ _ _ _ _ => rfl⟩

def words {m : ℕ} (c : Data) (d : ModeRead.Data m) (a : Fin 2) : Vector (List Bool) m :=
  Vector.ofFn fun i => FixedWidth.bits (addressValue c.width) (d.value i a).bits

@[simp] theorem words_get {m : ℕ} (c : Data) (d : ModeRead.Data m) (a : Fin 2) (i : Fin m) :
    (words c d a).get i = FixedWidth.bits (addressValue c.width) (d.value i a).bits := by
  simp [words,Vector.get,Fin.cast]

end Maxwell.Cost.CalibrationSource.Repack
