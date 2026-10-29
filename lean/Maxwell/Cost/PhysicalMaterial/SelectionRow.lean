import Maxwell.Cost.PhysicalMaterial.SelectPair
import Maxwell.Cost.PhysicalMaterial.SelectionSpec

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator
set_option maxHeartbeats 1600000

/-- Persistent cell coordinates and reusable membership work. -/
def Cell (s : BitRAMState) (cell : Fin 3 → ℕ) : Prop :=
  ∀ j, Word s (240+j.val) (cell j)
def TestReady (s : BitRAMState) : Prop := Blank s 290 ∧ Blank s 291 ∧ Blank s 292

def rowWork : Finset ℕ := targets ∪ {272, 273, 290, 291, 292, 302}
def testWork : Finset ℕ := {290, 291, 292}

/-- A proof interface for one fixed finite membership program. It contains no
runtime function calls; the composed row inserts the supplied finite code. -/
def TestCorrect {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (test : Code) (budget : ℕ) (input : List Bool) (tape : ℕ → Bool) : Prop :=
  ∀ row s, Ready s.val → Cell s.val cell → Bank s.val (value d row) → TestReady s.val →
    ∃ cost t, cost ≤ budget ∧ Executes input tape test cost s t ∧
      t.val.registers 2 = hit row ∧ Ready t.val ∧ TestReady t.val ∧ Frame testWork s.val t.val

def rowCode (test : Code) : Code := .seq readCode (.seq test
  (.seq selectPairCode (.seq clearCode (BankArray.incrementCode 302))))

def rowBudget (B testBudget : ℕ) : ℕ := 100000*(B+2)^2 + testBudget + 84*B+81

private theorem cell_frame {s t : BitRAMState} {cell : Fin 3 → ℕ}
    (h : Cell s cell) (hf : Frame rowWork s t) : Cell t cell := by
  intro j
  exact word_of_eq (hf.tapes (240+j.val) (by omega)
    (by simp [rowWork, targets]; omega)) (h j)

private theorem test_frame {s t : BitRAMState} (h : TestReady s)
    (hf : BinaryPrecision.Frame {272, 273} s t) : TestReady t :=
  ⟨blank_of_eq (hf.tapes 290 (by decide)) h.1,
    blank_of_eq (hf.tapes 291 (by decide)) h.2.1,
    blank_of_eq (hf.tapes 292 (by decide)) h.2.2⟩

/-- One fixed descriptor iteration loads, tests, selects, reclaims all five
candidate fields, and advances the stored record index. -/
theorem row {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (test : Code) (testBudget B : ℕ) (hd : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (hTest : TestCorrect d cell hit test testBudget input tape)
    (i : Fin n) (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (old : ℕ × ℕ) (holdB : old.1.bits.length ≤ B ∧ old.2.bits.length ≤ B)
    (s : Store) (hs : Ready s.val) (hdata : Stored d s.val)
    (hindex : BankArray.Word s.val 302 index) (hbank : Bank s.val (fun _ => 0))
    (hcell : Cell s.val cell) (htest : TestReady s.val) (hold : Pair s.val old) :
    ∃ cost t, cost ≤ rowBudget B testBudget ∧ Executes input tape (rowCode test) cost s t ∧
      Ready t.val ∧ Stored d t.val ∧ Bank t.val (fun _ => 0) ∧ Cell t.val cell ∧ TestReady t.val ∧
      Pair t.val (if hit i then strengthPair d i else old) ∧
      BankArray.Word t.val 302 (Increment.bits index) ∧ Frame rowWork s.val t.val := by
  obtain ⟨rc, a, hrc, er, ha, had, hav, fa⟩ := read d i B hd input tape index hi hil s hs hdata hindex hbank
  have fa' : Frame rowWork s.val a.val := fa.mono Finset.subset_union_left
  have hat : TestReady a.val :=
    ⟨blank_of_eq (fa.tapes 290 (by omega) (by decide)) htest.1,
      blank_of_eq (fa.tapes 291 (by omega) (by decide)) htest.2.1,
      blank_of_eq (fa.tapes 292 (by omega) (by decide)) htest.2.2⟩
  obtain ⟨tc, b, htc, et, hhit, hb, hbt, fb⟩ := hTest i a ha (cell_frame hcell fa') hav hat
  have fb' : Frame rowWork a.val b.val := fb.mono (by decide)
  have hbv : Bank b.val (value d i) := by
    intro j
    exact word_of_eq (fb.tapes (targetTape j) (by have := targetTape_bounds j; omega)
      (by fin_cases j <;> decide)) (hav j)
  have hbpair : Pair b.val old :=
    ⟨word_of_eq ((fb.tapes 272 (by omega) (by decide)).trans
      (fa.tapes 272 (by omega) (by decide))) hold.1,
      word_of_eq ((fb.tapes 273 (by omega) (by decide)).trans
      (fa.tapes 273 (by omega) (by decide))) hold.2⟩
  have vb (j : Fin 5) : (value d i j).bits.length ≤ B := (value_bits d i j s.val hdata).trans hd.2.1
  obtain ⟨pc, c, hpc, ep, hcp, fc⟩ := select_pair input tape old (strengthPair d i) (hit i) B
    ⟨holdB.1, holdB.2, vb 3, vb 4⟩ b hbpair (hbv 3) (hbv 4) hhit
  have hc : Ready c.val := fun j hj => blank_of_eq (fc.tapes j (by simp; omega)) (hb j hj)
  have hcv : Bank c.val (value d i) := by
    intro j
    exact word_of_eq (fc.tapes (targetTape j) (by fin_cases j <;> decide)) (hbv j)
  have fc' : Frame rowWork b.val c.val :=
    ⟨fc.memory, fc.inputHead, fc.randomCursor, fc.output,
      fun j _ hj => fc.tapes j (by intro hh; exact hj ((show {272, 273} ⊆ rowWork by decide) hh))⟩
  obtain ⟨cc, e, hcc, ec, he, hev, fe⟩ := clear input tape (value d i) B vb c hc hcv
  have fe' : Frame rowWork c.val e.val := fe.mono Finset.subset_union_left
  have fabce := ((fa'.trans fb').trans fc').trans fe'
  have hei : BankArray.Word e.val 302 index := by
    have keep : e.val.tapes 302 = s.val.tapes 302 :=
      (fe.tapes 302 (by omega) (by decide)).trans ((fc.tapes 302 (by decide)).trans
        ((fb.tapes 302 (by omega) (by decide)).trans (fa.tapes 302 (by omega) (by decide))))
    exact BankArray.word_of_eq keep hindex
  obtain ⟨ic, t, hic, ei, hti, _, htm, _, keep, fi⟩ := BankArray.increment_bank
    302 (by decide) input tape index e hei he.scratch
  have fi' : Frame rowWork e.val t.val :=
    ⟨htm, fi.1, fi.2.1, fi.2.2.1, fun j _ hj => keep j (by
      intro hh; subst j; exact hj (by decide))⟩
  have fall := fabce.trans fi'
  have htp : Pair t.val (if hit i then strengthPair d i else old) :=
    ⟨word_of_eq ((keep 272 (by decide)).trans (fe.tapes 272 (by omega) (by decide))) hcp.1,
      word_of_eq ((keep 273 (by decide)).trans (fe.tapes 273 (by omega) (by decide))) hcp.2⟩
  refine ⟨rc+(tc+(pc+(cc+ic))), t, ?_, er.seq (et.seq (ep.seq (ec.seq ei))),
    (fun j hj => blank_of_eq (keep j (by omega)) (he j hj)), ?_, ?_, cell_frame hcell fall,
    ?_, htp, hti, fall⟩
  · dsimp only [rowBudget]
    omega
  · refine ⟨BankArray.word_of_eq (fall.tapes 300 (by omega) (by decide)) hdata.width,
      BankArray.word_of_eq (fall.tapes 301 (by omega) (by decide)) hdata.clock, ?_, ?_⟩
    · intro j
      exact BankArray.word_of_eq (fall.tapes (baseTape j) (by simp only [baseTape]; omega)
        (by simp [rowWork, targets, baseTape]; omega)) (hdata.bases j)
    · intro j
      simpa only [fall.memory] using hdata.arrays j
  · intro j
    exact word_of_eq (keep (targetTape j) (by have := targetTape_bounds j; omega)) (hev j)
  · have hct := test_frame hbt fc
    exact ⟨blank_of_eq ((keep 290 (by decide)).trans (fe.tapes 290 (by omega) (by decide))) hct.1,
      blank_of_eq ((keep 291 (by decide)).trans (fe.tapes 291 (by omega) (by decide))) hct.2.1,
      blank_of_eq ((keep 292 (by decide)).trans (fe.tapes 292 (by omega) (by decide))) hct.2.2⟩

end Maxwell.Cost.PhysicalMaterial.Descriptors
