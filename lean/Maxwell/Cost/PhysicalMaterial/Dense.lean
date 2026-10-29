import Maxwell.Cost.PhysicalMaterial.Descriptors
import Maxwell.Cost.CalibrationMatrix.Rows

/-! Two actual dense arrays store the strength fraction at each physical cell.
They are filled once by local scatter and read once by the cell emitter. -/
namespace Maxwell.Cost.PhysicalMaterial.Dense
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

structure Layout (cells : ℕ) where
  width : List Bool
  clock : List Bool
  numBase : List Bool
  denBase : List Bool
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width
  separated : IncidenceEncoding.Separated (addressValue numBase) (cells*addressValue width)
    (addressValue denBase) (cells*addressValue width)

structure Stored {cells : ℕ} (l : Layout cells) (nums dens : Vector (List Bool) cells)
    (s : BitRAMState) : Prop where
  width : BankArray.Word s 300 l.width
  clock : BankArray.Word s 301 l.clock
  numBase : BankArray.Word s 320 l.numBase
  denBase : BankArray.Word s 321 l.denBase
  nums : BitArray.Represents s.memory (addressValue l.numBase) (addressValue l.width) nums
  dens : BitArray.Represents s.memory (addressValue l.denBase) (addressValue l.width) dens

def Layout.Sized {cells : ℕ} (l : Layout cells) (B : ℕ) : Prop :=
  l.width.length ≤ B ∧ addressValue l.width ≤ B ∧ l.numBase.length ≤ B ∧ l.denBase.length ≤ B

def writeCode : Code := .seq (BankArray.writeCanonicalCode 300 322 320 301 276)
  (BankArray.writeCanonicalCode 300 322 321 301 277)

private theorem ready_after {s t : BitRAMState} (h : Descriptors.Ready s)
    (hs : BankArray.Scratch t) (h7 : Blank t 7) (hf : BankArray.FrameExcept 37 s t) :
    Descriptors.Ready t := by
  intro i hi
  obtain ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩ := hs
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact blank_of_eq (hf.2.2.2.1 4 (by decide) (by decide)) (h 4 (by decide))
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

/-- Two charged indexed writes scatter the current descriptor's strength to
one known in-box cell. Both persistent scalar operands are preserved. -/
theorem write {cells : ℕ} (l : Layout cells) (nums dens : Vector (List Bool) cells)
    (i : Fin cells) (num den B : ℕ) (hl : l.Sized B)
    (hnum : num.bits.length ≤ addressValue l.width) (hden : den.bits.length ≤ addressValue l.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Descriptors.Ready s.val) (h37 : Blank s.val 37)
    (hd : Stored l nums dens s.val) (hindex : BankArray.Word s.val 322 index)
    (hnumWord : Word s.val 276 num) (hdenWord : Word s.val 277 den) :
    ∃ cost t, cost ≤ 80000*(B+2)^2 ∧ Executes input tape writeCode cost s t ∧
      Descriptors.Ready t.val ∧ Blank t.val 37 ∧
      Stored l (nums.set i (FixedWidth.bits (addressValue l.width) num.bits))
        (dens.set i (FixedWidth.bits (addressValue l.width) den.bits)) t.val ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (addressValue l.numBase+i.val*addressValue l.width)
          (FixedWidth.bits (addressValue l.width) num.bits))
        (addressValue l.denBase+i.val*addressValue l.width)
          (FixedWidth.bits (addressValue l.width) den.bits) ∧
      BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨nc, a, hnc, en, hnm, hna, has, ha7, ha37, fa⟩ := BankArray.write_canonical
    300 322 320 301 276 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape l.width index l.numBase l.clock nums i num
    l.width_nonempty hi l.clock_length l.width_positive hnum s hs.scratch (hs 7 (by decide)) h37
    hd.width hindex hd.numBase hd.clock hnumWord hd.nums
  have har := ready_after hs has ha7 fa
  have hda : BitArray.Represents a.val.memory (addressValue l.denBase) (addressValue l.width) dens := by
    rw [hnm]
    exact IncidenceEncoding.represents_write_disjoint hd.dens _ _ i _
      (FixedWidth.bits_length _ _) l.separated.symm
  have keepa (j : ℕ) (hj : 10 ≤ j) (h37 : j ≠ 37) : a.val.tapes j = s.val.tapes j :=
    fa.2.2.2.1 j (Or.inr hj) h37
  obtain ⟨dc, t, hdc, ed, hdm, hdd, hts, ht7, ht37, ft⟩ := BankArray.write_canonical
    300 322 321 301 277 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape l.width index l.denBase l.clock dens i den
    l.width_nonempty hi l.clock_length l.width_positive hden a has ha7 ha37
    (BankArray.word_of_eq (keepa 300 (by decide) (by decide)) hd.width)
    (BankArray.word_of_eq (keepa 322 (by decide) (by decide)) hindex)
    (BankArray.word_of_eq (keepa 321 (by decide) (by decide)) hd.denBase)
    (BankArray.word_of_eq (keepa 301 (by decide) (by decide)) hd.clock)
    (word_of_eq (keepa 277 (by decide) (by decide)) hdenWord) hda
  have frame : BankArray.FrameExcept 37 s.val t.val :=
    ⟨ft.1.trans fa.1, ft.2.1.trans fa.2.1, ft.2.2.1.trans fa.2.2.1,
      fun j hj hn => (ft.2.2.2.1 j hj hn).trans (fa.2.2.2.1 j hj hn),
      fun j hj h24 h25 h26 h27 h28 h29 => (ft.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
        (fa.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)⟩
  have hnt : BitArray.Represents t.val.memory (addressValue l.numBase) (addressValue l.width)
      (nums.set i (FixedWidth.bits (addressValue l.width) num.bits)) := by
    rw [hdm]
    exact IncidenceEncoding.represents_write_disjoint hna _ _ i _
      (FixedWidth.bits_length _ _) l.separated
  refine ⟨nc+dc, t, ?_, en.seq ed, ready_after har hts ht7 ft, ht37,
    ⟨BankArray.word_of_eq (frame.2.2.2.1 300 (by omega) (by decide)) hd.width,
      BankArray.word_of_eq (frame.2.2.2.1 301 (by omega) (by decide)) hd.clock,
      BankArray.word_of_eq (frame.2.2.2.1 320 (by omega) (by decide)) hd.numBase,
      BankArray.word_of_eq (frame.2.2.2.1 321 (by omega) (by decide)) hd.denBase,
      hnt, hdd⟩, by rw [hdm, hnm], frame⟩
  have hb := CalibrationMatrix.writeRow_cost_le l.width index l.numBase l.denBase num den B
    hl.1 hil hl.2.2.1 hl.2.2.2 hl.2.1
  omega

end Maxwell.Cost.PhysicalMaterial.Dense
