import Maxwell.Cost.CalibrationMatrix.Affine.Data

namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

variable {n : ℕ}

def value (words : Fin 10 → Vector (List Bool) n) (port : Fin 10) (row : Fin n) : ℕ :=
  addressValue ((words port).get row)
def newWPositive (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ := value words 0 row*d.K
def newWNegative (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ := value words 1 row*d.K
def partialPositive (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ :=
  newWPositive d words row+value words 2 row*d.K
def partialNegative (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ :=
  newWNegative d words row+value words 3 row*d.K
def newXPositive (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ :=
  partialPositive d words row+value words 5 row*d.S
def newXNegative (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) : ℕ :=
  partialNegative d words row+value words 4 row*d.S

def wWords (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) :=
  setPair words 6 7 row (FixedWidth.bits (addressValue d.width) (newWPositive d words row).bits)
    (FixedWidth.bits (addressValue d.width) (newWNegative d words row).bits)
def rowWords (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) :=
  setPair (wWords d words row) 8 9 row
    (FixedWidth.bits (addressValue d.width) (newXPositive d words row).bits)
    (FixedWidth.bits (addressValue d.width) (newXNegative d words row).bits)

def rowMemory (d : Data n) (words : Fin 10 → Vector (List Bool) n) (row : Fin n) (memory : ℕ → Bool) :=
  MemoryWord.writeBits (MemoryWord.writeBits
    (MemoryWord.writeBits (MemoryWord.writeBits memory
      (addressValue (d.bases 6)+row.val*addressValue d.width)
      (FixedWidth.bits (addressValue d.width) (newWPositive d words row).bits))
      (addressValue (d.bases 7)+row.val*addressValue d.width)
      (FixedWidth.bits (addressValue d.width) (newWNegative d words row).bits))
    (addressValue (d.bases 8)+row.val*addressValue d.width)
    (FixedWidth.bits (addressValue d.width) (newXPositive d words row).bits))
    (addressValue (d.bases 9)+row.val*addressValue d.width)
    (FixedWidth.bits (addressValue d.width) (newXNegative d words row).bits)

def rowCoreCode : Code := .seq (scaledTermCode 120 121 126)
  (.seq (writePairCode 128 129) (.seq (scaledTermCode 122 123 126)
    (.seq (scaledTermCode 125 124 127) writeRowCode)))

private theorem scaled_stored (d : Data n) (words : Fin 10 → Vector (List Bool) n)
    (a b : Fin 10) (scalarBank scalar B : ℕ) (hsBank : 100 ≤ scalarBank) (hs : scalar.bits.length ≤ B)
    (hd : d.Sized B) (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (row : Fin n) (hi : addressValue index = row.val) (hil : index.length ≤ B)
    (positive negative : ℕ) (hp : positive.bits.length ≤ B) (hn : negative.bits.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues positive negative)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (hscalar : RationalAccumulator.Word s.val scalarBank scalar) :
    ∃ cost t, cost ≤ 500000*(B+2)^2 ∧
      Executes input tape (scaledTermCode (baseBank a) (baseBank b) scalarBank) cost s t ∧
      Ready t.val (dotValues (positive+value words a row*scalar) (negative+value words b row*scalar)) ∧
      StepFrame s.val t.val := by
  exact scaled_term (baseBank a) (baseBank b) scalarBank
    (by have := baseBank_ge a; omega) (by have := baseBank_ge b; omega) hsBank
    input tape d.width index (d.bases a) (d.bases b) d.clock (words a) (words b) row
    d.width_nonempty hi d.clock_length positive negative scalar B hd.1 hd.2.1 hil
    (hd.2.2.1 a) (hd.2.2.1 b) hp hn hs s hr hdata.width hindex
    (hdata.bases a) (hdata.bases b) hdata.clock hscalar (hdata.arrays a) (hdata.arrays b)

private theorem row_word {s t : BitRAMState} (hf : RowFrame s t) (i : ℕ) (hi : 100 ≤ i)
    {bits : List Bool} (hw : BankArray.Word s i bits) : BankArray.Word t i bits :=
  BankArray.word_of_eq (hf.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega)) hw

private theorem step_blank {s t : BitRAMState} (hf : StepFrame s t) (h37 : Blank s 37) : Blank t 37 :=
  RationalAccumulator.blank_of_eq (hf.2.2.2.2.1 37 (Or.inr (by omega)) (Or.inr (by omega))) h37

private theorem bits_mono {a b : ℕ} (hab : a ≤ b) : a.bits.length ≤ b.bits.length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size hab

/-- One actual affine row reuses K*w in both output vectors. The negative
S*u term is implemented by swapping its two input channels. -/
theorem row_core (d : Data n) (words : Fin 10 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (row : Fin n)
    (hwp : (newWPositive d words row).bits.length ≤ addressValue d.width)
    (hwn : (newWNegative d words row).bits.length ≤ addressValue d.width)
    (hxp : (newXPositive d words row).bits.length ≤ addressValue d.width)
    (hxn : (newXNegative d words row).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = row.val) (hil : index.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 1800000*(B+2)^2 ∧ Executes input tape rowCoreCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (rowWords d words row) t.val ∧
      BankArray.Word t.val 104 index ∧ Blank t.val 37 ∧
      t.val.tapes 108 = s.val.tapes 108 ∧
      t.val.memory = rowMemory d words row s.val.memory ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧ MatrixFrame s.val t.val := by
  obtain ⟨c1, a, hc1, ea, har, haf⟩ := scaled_stored d words 0 1 126 d.K B (by omega) hd.2.2.2.1 hd
    input tape index row hi hil 0 0 (by simp) (by simp) s hr hdata hindex hdata.K
  have har' : Ready a.val (dotValues (newWPositive d words row) (newWNegative d words row)) := by
    simpa only [newWPositive, newWNegative, Nat.zero_add] using har
  have had := hdata.of_step haf
  have hai := frame_word haf 104 (by omega) hindex
  obtain ⟨c2, b, hc2, eb, hbr, hb37, hbm, hbpa, hbna, hbf⟩ := write_pair 128 129
    (by omega) (by omega) input tape d.width index (d.bases 6) (d.bases 7) d.clock
    (words 6) (words 7) row (newWPositive d words row) (newWNegative d words row)
    d.width_nonempty hi d.clock_length d.width_positive hwp hwn (d.separated 6 7 (by decide))
    a har' (step_blank haf h37) had.width hai (had.bases 6) (had.bases 7) had.clock
    (had.arrays 6) (had.arrays 7)
  have hbd : Stored d (wWords d words row) b.val := had.after_pair 6 7 (by decide) row _ _
    (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) hbf hbm hbpa hbna
  have hbi := row_word hbf 104 (by omega) hai
  obtain ⟨c3, c, hc3, ec, hcr, hcf⟩ := scaled_stored d (wWords d words row) 2 3 126 d.K B
    (by omega) hd.2.2.2.1 hd input tape index row hi hil
    (newWPositive d words row) (newWNegative d words row) (hwp.trans hd.2.1) (hwn.trans hd.2.1)
    b hbr hbd hbi hbd.K
  have hcr' : Ready c.val (dotValues (partialPositive d words row) (partialNegative d words row)) := by
    simpa [partialPositive, partialNegative, value, wWords, setPair] using hcr
  have hcd := hbd.of_step hcf
  have hci := frame_word hcf 104 (by omega) hbi
  have hpp : (partialPositive d words row).bits.length ≤ B :=
    (bits_mono (Nat.le_add_right _ (value words 5 row*d.S))).trans (hxp.trans hd.2.1)
  have hpn : (partialNegative d words row).bits.length ≤ B :=
    (bits_mono (Nat.le_add_right _ (value words 4 row*d.S))).trans (hxn.trans hd.2.1)
  obtain ⟨c4, e, hc4, ee, her, hef⟩ := scaled_stored d (wWords d words row) 5 4 127 d.S B
    (by omega) hd.2.2.2.2 hd input tape index row hi hil
    (partialPositive d words row) (partialNegative d words row) hpp hpn c hcr' hcd hci hcd.S
  have her' : Ready e.val (dotValues (newXPositive d words row) (newXNegative d words row)) := by
    simpa [newXPositive, newXNegative, value, wWords, setPair] using her
  have hed := hcd.of_step hef
  have hei := frame_word hef 104 (by omega) hci
  obtain ⟨c5, t, hc5, et, htr, ht37, htm, htpa, htna, htf⟩ := write_row input tape
    d.width index (d.bases 8) (d.bases 9) d.clock ((wWords d words row) 8) ((wWords d words row) 9)
    row (newXPositive d words row) (newXNegative d words row) d.width_nonempty hi d.clock_length
    d.width_positive hxp hxn (d.separated 8 9 (by decide)) e her'
    (step_blank hef (step_blank hcf hb37)) hed.width hei (hed.bases 8) (hed.bases 9) hed.clock
    (hed.arrays 8) (hed.arrays 9)
  have htd : Stored d (rowWords d words row) t.val := hed.after_pair 8 9 (by decide) row _ _
    (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) htf htm htpa htna
  refine ⟨c1+(c2+(c3+(c4+c5))), t, ?_, ea.seq (eb.seq (ec.seq (ee.seq et))), htr, htd,
    row_word htf 104 (by omega) hei, ht37, ?_, ?_, ?_, ?_⟩
  · have hwc := writeRow_cost_le d.width index (d.bases 6) (d.bases 7)
      (newWPositive d words row) (newWNegative d words row) B hd.1 hil (hd.2.2.1 6) (hd.2.2.1 7) hd.2.1
    have hxc := writeRow_cost_le d.width index (d.bases 8) (d.bases 9)
      (newXPositive d words row) (newXNegative d words row) B hd.1 hil (hd.2.2.1 8) (hd.2.2.1 9) hd.2.1
    omega
  · exact (htf.2.2.2.1 108 (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
      ((hef.2.2.2.2.1 108 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hcf.2.2.2.2.1 108 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hbf.2.2.2.1 108 (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
      (haf.2.2.2.2.1 108 (Or.inr (by omega)) (Or.inr (by omega))))))
  · simp only [htm, hef.1, hcf.1, hbm, haf.1, rowMemory]
  · intro j hj
    exact (htf.2.2.2.1 j (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
      ((hef.2.2.2.2.1 j (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hcf.2.2.2.2.1 j (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hbf.2.2.2.1 j (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
      (haf.2.2.2.2.1 j (Or.inr (by omega)) (Or.inr (by omega))))))
  · exact ((((MatrixFrame.of_loop (LoopFrame.of_step haf)).trans (MatrixFrame.of_row hbf)).trans
      (MatrixFrame.of_loop (LoopFrame.of_step hcf))).trans
      (MatrixFrame.of_loop (LoopFrame.of_step hef))).trans (MatrixFrame.of_row htf)

end Maxwell.Cost.CalibrationMatrix.Affine
