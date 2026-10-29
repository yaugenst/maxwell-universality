import Maxwell.Cost.CalibrationMatrix.Scale.Data

namespace Maxwell.Cost.CalibrationMatrix.Scale
open Structured
open RationalAccumulator (Blank)
open Maxwell.Cost.CalibrationMatrix.Affine (scaledTermCode writePairCode)
set_option maxHeartbeats 1500000
variable {n : ℕ}

def value (words : Fin 4 → Vector (List Bool) n) (port : Fin 4) (i : Fin n) : ℕ :=
  addressValue ((words port).get i)
def positive (d : Data n) (words : Fin 4 → Vector (List Bool) n) (i : Fin n) := value words 0 i*d.K
def negative (d : Data n) (words : Fin 4 → Vector (List Bool) n) (i : Fin n) := value words 1 i*d.K
def rowWords (d : Data n) (words : Fin 4 → Vector (List Bool) n) (i : Fin n) :=
  setPair words 2 3 i (FixedWidth.bits (addressValue d.width) (positive d words i).bits)
    (FixedWidth.bits (addressValue d.width) (negative d words i).bits)
def rowMemory (d : Data n) (words : Fin 4 → Vector (List Bool) n) (i : Fin n) (memory : ℕ → Bool) :=
  MemoryWord.writeBits (MemoryWord.writeBits memory
    (addressValue (d.bases 2)+i.val*addressValue d.width)
    (FixedWidth.bits (addressValue d.width) (positive d words i).bits))
    (addressValue (d.bases 3)+i.val*addressValue d.width)
    (FixedWidth.bits (addressValue d.width) (negative d words i).bits)
def rowCode : Code := .seq (scaledTermCode 120 121 126)
  (.seq (writePairCode 128 129) (.seq clearDotCode (BankArray.incrementCode 104)))

theorem row (d : Data n) (words : Fin 4 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B) (i : Fin n)
    (hp : (positive d words i).bits.length ≤ addressValue d.width)
    (hneg : (negative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 700000*(B+2)^2 ∧ Executes input tape rowCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (rowWords d words i) t.val ∧
      BankArray.Word t.val 104 (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      Blank t.val 37 ∧ t.val.tapes 108 = s.val.tapes 108 ∧
      t.val.memory = rowMemory d words i s.val.memory ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧ MatrixFrame s.val t.val := by
  obtain ⟨c1, a, hc1, ea, har, haf⟩ := Affine.scaled_term 120 121 126
    (by omega) (by omega) (by omega) input tape d.width index (d.bases 0) (d.bases 1)
    d.clock (words 0) (words 1) i d.width_nonempty hi d.clock_length 0 0 d.K B
    hd.1 hd.2.1 hil (hd.2.2.1 0) (hd.2.2.1 1) (by simp) (by simp) hd.2.2.2
    s hr hdata.width hindex (hdata.bases 0) (hdata.bases 1) hdata.clock hdata.K
    (hdata.arrays 0) (hdata.arrays 1)
  have har' : Ready a.val (dotValues (positive d words i) (negative d words i)) := by
    simpa only [positive, negative, value, Nat.zero_add] using har
  have had := hdata.of_step haf
  have hai := Affine.frame_word haf 104 (by omega) hindex
  have ha37 := RationalAccumulator.blank_of_eq
    (haf.2.2.2.2.1 37 (Or.inr (by omega)) (Or.inr (by omega))) h37
  obtain ⟨c2, b, hc2, eb, hbr, hb37, hbm, hbpa, hbna, hbf⟩ := Affine.write_pair 128 129
    (by omega) (by omega) input tape d.width index (d.bases 2) (d.bases 3) d.clock
    (words 2) (words 3) i (positive d words i) (negative d words i)
    d.width_nonempty hi d.clock_length d.width_positive hp hneg (d.separated 2 3 (by decide))
    a har' ha37 had.width hai (had.bases 2) (had.bases 3) had.clock (had.arrays 2) (had.arrays 3)
  have hbd : Stored d (rowWords d words i) b.val := had.after_pair 2 3 (by decide) i _ _
    (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) hbf hbm hbpa hbna
  obtain ⟨c, ec, hcr, hc37, hcm, hcf⟩ := clear_dot input tape (positive d words i) (negative d words i) b hbr hb37
  have keepBC (j : ℕ) (hj : 100 ≤ j) : c.val.tapes j = a.val.tapes j :=
    (hcf.2.2.2.1 j (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
      (hbf.2.2.2.1 j (Or.inr (by omega)) (by omega) (by omega) (by omega))
  have hcd := hbd.of_tapes_memory hcm (fun j hj =>
    hcf.2.2.2.1 j (Or.inr (by omega)) (by omega) (by omega) (by omega))
  have hci := BankArray.word_of_eq (keepBC 104 (by omega)) hai
  obtain ⟨c3, t, hc3, et, hti, _, htm, _, keep, ft⟩ := BankArray.increment_bank
    104 (by omega) input tape index c hci hcr.2.1
  have frame : MatrixFrame c.val t.val :=
    ⟨ft.1, ft.2.1, ft.2.2.1, fun j hj _ _ _ _ h104 _ _ => ft.2.2.2.1 j hj h104, ft.2.2.2.2⟩
  refine ⟨c1+(c2+(6*((positive d words i).bits.length+(negative d words i).bits.length)+8+c3)), t,
    ?_, ea.seq (eb.seq (ec.seq et)), hcr.of_tapes (fun j hj => keep j (by omega)),
    hcd.of_tapes_memory htm (fun j hj => keep j (by omega)), hti,
    BankArray.increment_length_bound index B hil (by rw [hi]; omega),
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) hc37, ?_, ?_,
    (fun j hj => (keep j (by omega)).trans ((keepBC j (by omega)).trans
      (haf.2.2.2.2.1 j (Or.inr (by omega)) (Or.inr (by omega))))),
    (((MatrixFrame.of_loop (LoopFrame.of_step haf)).trans (MatrixFrame.of_row hbf)).trans
      (MatrixFrame.of_row hcf)).trans frame⟩
  · have hwc := writeRow_cost_le d.width index (d.bases 2) (d.bases 3)
      (positive d words i) (negative d words i) B hd.1 hil (hd.2.2.1 2) (hd.2.2.1 3) hd.2.1
    have hquad : B+2 ≤ (B+2)^2 := by nlinarith
    nlinarith [hd.2.1]
  · exact (keep 108 (by omega)).trans ((keepBC 108 (by omega)).trans
      (haf.2.2.2.2.1 108 (Or.inr (by omega)) (Or.inr (by omega))))
  · rw [htm, hcm, hbm, haf.1]
    rfl

end Maxwell.Cost.CalibrationMatrix.Scale
