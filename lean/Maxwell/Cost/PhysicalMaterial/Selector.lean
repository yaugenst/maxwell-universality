import Maxwell.Cost.PhysicalMaterial.SelectionLoop

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def selectorCode (test : Code) : Code := .seq (BinaryPrecision.literalCode 273 1)
  (.seq (.call (WordTransfer.clone 304 303)) (scanCode test))

def selectorBudget (n B testBudget : ℕ) : ℕ := scanBudget n B testBudget + 15*B+34

/-- Initialize the selected fraction to zero and copy the actual stored record
count. The fixed finite selector contains no input-dependent unrolled code. -/
theorem select {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (test : Code) (testBudget B : ℕ) (hd : d.Sized B) (hn : n < 2^B)
    (input : List Bool) (tape : ℕ → Bool) (hTest : TestCorrect d cell hit test testBudget input tape)
    (s : Store) (hs : Ready s.val) (hdata : Stored d s.val) (hcount : Word s.val 304 n)
    (hbank : Bank s.val (fun _ => 0)) (hcell : Cell s.val cell) (htest : TestReady s.val)
    (h272 : Blank s.val 272) (h273 : Blank s.val 273)
    (h302 : Blank s.val 302) (h303 : Blank s.val 303) :
    ∃ cost t, cost ≤ selectorBudget n B testBudget ∧ Executes input tape (selectorCode test) cost s t ∧
      Ready t.val ∧ Stored d t.val ∧ Bank t.val (fun _ => 0) ∧ Cell t.val cell ∧ TestReady t.val ∧
      Pair t.val (selectedThrough d hit n) ∧ Blank t.val 302 ∧ Blank t.val 303 ∧
      Frame scanWork s.val t.val := by
  obtain ⟨a, ea, ha273, fa⟩ := BinaryPrecision.literal 273 1 input tape s h273
  obtain ⟨no, hno⟩ := hcount
  obtain ⟨co, hco⟩ := h303
  have ha304 : a.val.tapes 304 = BitTape.shifted n.bits no := (fa.tapes 304 (by decide)).trans hno
  have ha303 : a.val.tapes 303 = {BitTape.blank with head := co} :=
    (fa.tapes 303 (by decide)).trans hco
  obtain ⟨b, eb, hbt, fb⟩ := WordCall.clone 304 303 (by decide) input tape n.bits no co a ha304 ha303
  have keep (j : ℕ) (h273 : j ≠ 273) (h303 : j ≠ 303) : b.val.tapes j = s.val.tapes j := by
    rw [hbt, Function.update_of_ne h303]
    exact fa.tapes j (by simpa using h273)
  have frame : Frame scanWork s.val b.val := by
    refine ⟨fb.2.2.1.trans fa.memory, fb.2.1.trans fa.inputHead,
      fb.2.2.2.1.trans fa.randomCursor, fb.2.2.2.2.1.trans fa.output, ?_⟩
    intro j _ hj
    apply keep j
    · intro he; subst j; exact hj (by decide)
    · intro he; subst j; exact hj (by decide)
  have hbr : Ready b.val := fun j hj => blank_of_eq (keep j (by omega) (by omega)) (hs j hj)
  have hbd : Stored d b.val := by
    refine ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) hdata.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) hdata.clock, ?_, ?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (baseTape j) (by simp only [baseTape]; omega)
        (by simp only [baseTape]; omega)) (hdata.bases j)
    · intro j
      simpa only [frame.memory] using hdata.arrays j
  have hbv : Bank b.val (fun _ => 0) := by
    intro j
    exact word_of_eq (keep (targetTape j) (by have := targetTape_bounds j; omega)
      (by have := targetTape_bounds j; omega)) (hbank j)
  have hbc : Cell b.val cell := fun j => word_of_eq (keep (240+j.val) (by omega) (by omega)) (hcell j)
  have hbtReady : TestReady b.val :=
    ⟨blank_of_eq (keep 290 (by decide) (by decide)) htest.1,
      blank_of_eq (keep 291 (by decide) (by decide)) htest.2.1,
      blank_of_eq (keep 292 (by decide) (by decide)) htest.2.2⟩
  have hbp : Pair b.val (0, 1) :=
    ⟨(zero_word_iff_blank _ _).mpr (blank_of_eq (keep 272 (by decide) (by decide)) h272),
      word_of_eq (by simp [hbt]) ha273⟩
  obtain ⟨io, hio⟩ := h302
  have hbi : BankArray.Word b.val 302 [] := ⟨io, by simpa using (keep 302 (by decide) (by decide)).trans hio⟩
  have hbcounter : b.val.tapes 303 = BitTape.shifted n.bits co := by simp [hbt]
  have hnlen : n.bits.length ≤ B := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hn
  obtain ⟨cost, t, hcost, et, htr, htd, htv, htc, htt, htp, ht302, ht303, ft⟩ :=
    scan d cell hit test testBudget B hd hn input tape hTest [] n.bits rfl
      (addressValue_bits n) (by simp) hnlen co b hbr hbd hbi hbcounter hbv hbc hbtReady hbp
  refine ⟨(10*(1 : ℕ).bits.length+7)+((15*n.bits.length+17)+cost), t, ?_,
    ea.seq (eb.seq et), htr, htd, htv, htc, htt, htp, ht302, ht303, frame.trans ft⟩
  rw [show (1 : ℕ).bits.length = 1 from by decide]
  dsimp only [selectorBudget]
  omega

/-- A priced execution of the compiled, finite selector. -/
theorem select_run {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (test : Code) (testBudget B : ℕ) (hd : d.Sized B) (hn : n < 2^B)
    (input : List Bool) (tape : ℕ → Bool) (hTest : TestCorrect d cell hit test testBudget input tape)
    (s : Store) (hs : Ready s.val) (hdata : Stored d s.val) (hcount : Word s.val 304 n)
    (hbank : Bank s.val (fun _ => 0)) (hcell : Cell s.val cell) (htest : TestReady s.val)
    (h272 : Blank s.val 272) (h273 : Blank s.val 273)
    (h302 : Blank s.val 302) (h303 : Blank s.val 303) :
    ∃ t : Store, (runPriced ((selectorCode test).compile.next input tape)
      (selectorBudget n B testBudget+1) s.val).finished = some (t.place (selectorCode test).size) ∧
      (runPriced ((selectorCode test).compile.next input tape)
        (selectorBudget n B testBudget+1) s.val).instructions ≤ selectorBudget n B testBudget ∧
      Pair t.val (selectedThrough d hit n) := by
  obtain ⟨cost, t, hcost, he, _, _, _, _, _, hp, _⟩ :=
    select d cell hit test testBudget B hd hn input tape hTest s hs hdata hcount hbank hcell htest
      h272 h273 h302 h303
  have hr := he.compiled_run (selectorBudget n B testBudget+1) (by omega)
  exact ⟨t, hr.1, hr.2.symm ▸ hcost, hp⟩

end Maxwell.Cost.PhysicalMaterial.Descriptors
