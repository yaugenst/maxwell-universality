import Maxwell.Cost.IndexedAddress.Finish
import Maxwell.Cost.Counter

namespace Maxwell.Cost.IndexedAddress
open Structured

/-- Indexed array addresses are computed by actual multiplication, addition,
padding, transfers and scans. No integer-address primitive is introduced. -/
def code : Code := .seq prepareCode finishCode

def program : BitRAM := code.compile

theorem value_lt_pow_length (word : List Bool) : addressValue word < 2 ^ word.length := by
  induction word with
  | nil => simp [addressValue]
  | cons b word ih =>
    cases b <;> simp only [addressValue, List.length_cons, pow_succ, Bool.toNat_false,
      Bool.toNat_true] <;> omega

theorem product_length_le (width index : List Bool) :
    (addressValue width * addressValue index).bits.length ≤ width.length + index.length := by
  rw [Nat.size_eq_bits_len, Nat.size_le, pow_add]
  have hw := value_lt_pow_length width
  have hi := value_lt_pow_length index
  exact Nat.mul_lt_mul_of_lt_of_lt hw hi

theorem sum_length_le (xs ys : List Bool) :
    (addressValue xs + addressValue ys).bits.length ≤ xs.length + ys.length + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le, pow_succ]
  have hx : addressValue xs < 2 ^ (xs.length + ys.length) :=
    (value_lt_pow_length xs).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hy : addressValue ys < 2 ^ (xs.length + ys.length) :=
    (value_lt_pow_length ys).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  omega

/-- A complete structured execution of the finite indexed-address program.
Width and base values remain available for repeated array accesses. -/
theorem executes (input : List Bool) (tape : ℕ → Bool)
    (width index base : List Bool) (ao wo zo yo io bo savedOrigin : ℤ)
    (hwidth : 0 < width.length) (s : Store)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted width wo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = {BitTape.blank with head := yo})
    (h5 : s.val.tapes 5 = BitTape.shifted index io)
    (h8 : s.val.tapes 8 = BitTape.shifted base bo)
    (h9 : s.val.tapes 9 = {BitTape.blank with head := savedOrigin}) :
    ∃ cost t resultOrigin scratchOrigin addressOrigin widthOrigin,
      cost ≤ 1000 * (width.length + index.length + base.length + 5)^2 ∧
      Executes input tape code cost s t ∧
      t.val.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.val.tapes 1 = BitTape.shifted width widthOrigin ∧
      t.val.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.val.tapes 3 = {BitTape.blank with head := yo + index.length} ∧
      t.val.tapes 5 = BitTape.shiftedEnd
        (addressValue base + addressValue width * addressValue index).bits addressOrigin ∧
      t.val.tapes 8 = BitTape.shifted base bo ∧
      t.val.tapes 9 = {BitTape.blank with head := savedOrigin + width.length} ∧ Frame s.val t.val := by
  let product := (addressValue width * addressValue index).bits
  obtain ⟨pcost, p, ro, so, hpcost, hp, hp0, hp1, hp2, hp3, hp5, hp9, hpf⟩ :=
    prepare input tape width index base ao wo zo yo io bo savedOrigin hwidth s h0 h1 h2 h3 h5 h8 h9
  obtain ⟨fcost, t, hfcost, hf, ht0, ht1, ht2, ht3, ht5, ht9, htf⟩ :=
    finish input tape (PadWord.bits base) (PadWord.bits product) width ro (wo + width.length)
      so (io + index.length) savedOrigin (PadWord.nonempty base) (PadWord.nonempty product)
      p hp0 hp1 hp2 hp5 hp9
  have hval : addressValue (PadWord.bits base) + addressValue (PadWord.bits product) =
      addressValue base + addressValue width * addressValue index := by
    simp [product, addressValue_bits]
  have hprod := product_length_le width index
  have hbpad := PadWord.length_le base
  have hppad := PadWord.length_le product
  have hsum := sum_length_le (PadWord.bits base) (PadWord.bits product)
  refine ⟨pcost + fcost, t, ro + (PadWord.bits product).length,
    so + (addressValue base + addressValue width * addressValue index).bits.length,
    io + index.length + (PadWord.bits product).length,
    wo + width.length + (PadWord.bits base).length, ?_, hp.seq hf, ht0, ht1,
    by simpa only [hval] using ht2, ht3.trans hp3, by simpa only [hval] using ht5,
    ((hpf.trans htf).2.2.2.2.2.1 8 (by omega) (by omega) (by omega)).trans h8,
    ht9, hpf.trans htf⟩
  have hquad : 500 * (width.length + index.length + 2)^2 ≤
      500 * (width.length + index.length + base.length + 5)^2 := by
    exact Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2)
  dsimp [product] at hppad hsum hfcost
  nlinarith

/-- The structured semantics compiles to a single fixed finite BitRAM with
exact charged steps and a polynomial cap in operand bit lengths. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (width index base : List Bool) (ao wo zo yo io bo savedOrigin : ℤ)
    (hwidth : 0 < width.length) (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted width wo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = {BitTape.blank with head := yo})
    (h5 : s.tapes 5 = BitTape.shifted index io)
    (h8 : s.tapes 8 = BitTape.shifted base bo)
    (h9 : s.tapes 9 = {BitTape.blank with head := savedOrigin}) :
    ∃ cost t resultOrigin scratchOrigin addressOrigin widthOrigin,
      cost ≤ 1000 * (width.length + index.length + base.length + 5)^2 ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = code.size ∧
      t.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.tapes 1 = BitTape.shifted width widthOrigin ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 3 = {BitTape.blank with head := yo + index.length} ∧
      t.tapes 5 = BitTape.shiftedEnd
        (addressValue base + addressValue width * addressValue index).bits addressOrigin ∧
      t.tapes 8 = BitTape.shifted base bo ∧
      t.tapes 9 = {BitTape.blank with head := savedOrigin + width.length} ∧ Frame s t := by
  obtain ⟨cost, t, ro, so, io', wo', hc, hs, ht0, ht1, ht2, ht3, ht5, ht8, ht9, hf⟩ :=
    executes input tape width index base ao wo zo yo io bo savedOrigin hwidth
      ⟨s, hpc⟩ h0 h1 h2 h3 h5 h8 h9
  exact ⟨cost, t.place code.size, ro, so, io', wo', hc, hs.compiled_steps, rfl,
    ht0, ht1, ht2, ht3, ht5, ht8, ht9, hf⟩

/-- Capped execution retains the computed address, reusable operands and
cleared scratch tapes, so subsequent indexed reads/writes can be linked. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (width index base : List Bool) (ao wo zo yo io bo savedOrigin : ℤ)
    (hwidth : 0 < width.length) (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted width wo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = {BitTape.blank with head := yo})
    (h5 : s.tapes 5 = BitTape.shifted index io)
    (h8 : s.tapes 8 = BitTape.shifted base bo)
    (h9 : s.tapes 9 = {BitTape.blank with head := savedOrigin}) :
    ∃ t resultOrigin scratchOrigin addressOrigin widthOrigin,
      (runPriced (program.next input tape)
        (1000 * (width.length + index.length + base.length + 5)^2 + 1) s).finished = some t ∧
      (runPriced (program.next input tape)
        (1000 * (width.length + index.length + base.length + 5)^2 + 1) s).instructions ≤
          1000 * (width.length + index.length + base.length + 5)^2 ∧
      t.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.tapes 1 = BitTape.shifted width widthOrigin ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 3 = {BitTape.blank with head := yo + index.length} ∧
      t.tapes 5 = BitTape.shiftedEnd
        (addressValue base + addressValue width * addressValue index).bits addressOrigin ∧
      t.tapes 8 = BitTape.shifted base bo ∧
      t.tapes 9 = {BitTape.blank with head := savedOrigin + width.length} ∧ Frame s t := by
  obtain ⟨cost, t, ro, so, io', wo', hc, hs, ht0, ht1, ht2, ht3, ht5, ht8, ht9, hf⟩ :=
    executes input tape width index base ao wo zo yo io bo savedOrigin hwidth
      ⟨s, hpc⟩ h0 h1 h2 h3 h5 h8 h9
  have hrun := hs.compiled_run (1000 * (width.length + index.length + base.length + 5)^2 + 1) (by omega)
  exact ⟨t.place code.size, ro, so, io', wo', hrun.1, hrun.2.symm ▸ hc,
    ht0, ht1, ht2, ht3, ht5, ht8, ht9, hf⟩

end Maxwell.Cost.IndexedAddress
