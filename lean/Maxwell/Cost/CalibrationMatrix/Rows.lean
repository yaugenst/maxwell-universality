import Maxwell.Cost.CalibrationMatrix.Dot
import Maxwell.Cost.CalibrationMatrix.WriteRow

namespace Maxwell.Cost.CalibrationMatrix

open Structured

structure OutputLayout where
  positiveBase : List Bool
  negativeBase : List Bool

def OutputLayout.Sized (l : OutputLayout) (B : ℕ) : Prop :=
  l.positiveBase.length ≤ B ∧ l.negativeBase.length ≤ B

def OutputLayout.Separated (l : OutputLayout) (rows width : ℕ) : Prop :=
  IncidenceEncoding.Separated (addressValue l.positiveBase) (rows*width)
    (addressValue l.negativeBase) (rows*width)

structure OutputStored {rows : ℕ} (l : OutputLayout) (width : ℕ) (index : List Bool)
    (positive negative : Vector (List Bool) rows) (s : BitRAMState) : Prop where
  index : BankArray.Word s 104 index
  positiveBase : BankArray.Word s 114 l.positiveBase
  negativeBase : BankArray.Word s 115 l.negativeBase
  positive : BitArray.Represents s.memory (addressValue l.positiveBase) width positive
  negative : BitArray.Represents s.memory (addressValue l.negativeBase) width negative

theorem OutputStored.of_loop {rows : ℕ} {l : OutputLayout} {width : ℕ} {index : List Bool}
    {positive negative : Vector (List Bool) rows} {s t : BitRAMState}
    (h : OutputStored l width index positive negative s) (hf : LoopFrame s t) :
    OutputStored l width index positive negative t := by
  have keep (i : ℕ) (hi : i = 104 ∨ 110 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  exact ⟨BankArray.word_of_eq (keep 104 (by omega)) h.index,
    BankArray.word_of_eq (keep 114 (by omega)) h.positiveBase,
    BankArray.word_of_eq (keep 115 (by omega)) h.negativeBase,
    by simpa only [hf.1] using h.positive, by simpa only [hf.1] using h.negative⟩

def MatrixFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ≠ 37 →
    i ≠ 102 → i ≠ 103 → i ≠ 104 → i ≠ 106 → i ≠ 108 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem MatrixFrame.refl (s : BitRAMState) : MatrixFrame s s := by simp [MatrixFrame]

theorem MatrixFrame.trans {s t u : BitRAMState} (h : MatrixFrame s t) (k : MatrixFrame t u) :
    MatrixFrame s u := by
  rcases h with ⟨hi, hr, ho, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hi hj hk hl hm hn hp hq =>
      (kt i hi hj hk hl hm hn hp hq).trans (ht i hi hj hk hl hm hn hp hq),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem MatrixFrame.of_loop {s t : BitRAMState} (h : LoopFrame s t) : MatrixFrame s t :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1,
    fun i hi hj _ h102 h103 _ h106 _ => h.2.2.2.2.1 i hi hj h102 h103 h106, h.2.2.2.2.2⟩

theorem MatrixFrame.of_row {s t : BitRAMState} (h : RowFrame s t) : MatrixFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1,
    fun i hi hj h37 _ _ _ _ _ => h.2.2.2.1 i hi (by omega) (by omega) h37, h.2.2.2.2⟩

theorem MatrixFrame.of_counter {s t : Store} (h : CountedShifted.Frame 108 s t) :
    MatrixFrame s.val t.val := by
  rcases h with ⟨_, hi, _, hr, ho, ht, hg⟩
  exact ⟨hi, hr, ho, fun i _ _ _ _ _ _ _ h108 => ht i h108,
    fun i hi h24 h25 _ _ _ h29 => hg i (by omega) h24 h25 h29⟩

theorem Stored.of_matrix {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (hm : t.memory = s.memory) (hf : MatrixFrame s t) : Stored d t := by
  have keep (i : ℕ) (hi : i = 100 ∨ i = 101 ∨ 110 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    BankArray.word_of_eq (keep 110 (by omega)) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by omega)) h.matrixNegativeBase,
    BankArray.word_of_eq (keep 112 (by omega)) h.vectorPositiveBase,
    BankArray.word_of_eq (keep 113 (by omega)) h.vectorNegativeBase,
    by simpa only [hm] using h.matrixPositive,
    by simpa only [hm] using h.matrixNegative,
    by simpa only [hm] using h.vectorPositive,
    by simpa only [hm] using h.vectorNegative⟩

theorem writeRow_cost_le (width index positiveBase negativeBase : List Bool) (p n B : ℕ)
    (hw : width.length ≤ B) (hi : index.length ≤ B)
    (hp : positiveBase.length ≤ B) (hn : negativeBase.length ≤ B) (hW : addressValue width ≤ B) :
    BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) p.bits) +
      BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) n.bits) +
      220*addressValue width+220 ≤ 80000*(B+2)^2 := by
  have access (base : List Bool) (value : ℕ) (hb : base.length ≤ B) :
      BankArray.costCap width index base (FixedWidth.bits (addressValue width) value.bits) ≤
        30000*(B+2)^2 := by
    calc
      _ ≤ 1000*(B+B+B+5)^2 + B*(15*(B+B+B+1+B)+24) + 4 + 40*(B+B+B+B+B+3) := by
        dsimp [BankArray.costCap, ArrayAccess.costCap]
        rw [FixedWidth.bits_length]
        gcongr
      _ ≤ _ := by nlinarith
  have ha := access positiveBase p hp
  have hb := access negativeBase n hn
  nlinarith

end Maxwell.Cost.CalibrationMatrix
