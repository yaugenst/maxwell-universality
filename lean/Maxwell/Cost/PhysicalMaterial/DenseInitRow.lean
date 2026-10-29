import Maxwell.Cost.PhysicalMaterial.DenseFill

namespace Maxwell.Cost.PhysicalMaterial.Dense
open Structured RationalAccumulator
set_option maxHeartbeats 1300000

/-- Control frame for initialization of the dense strength table. -/
structure InitFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j = 4 ∨ 10 ≤ j → j ≠ 37 → j ≠ 322 → j ≠ 329 → t.tapes j = s.tapes j

theorem InitFrame.refl (s : BitRAMState) : InitFrame s s := ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
theorem InitFrame.trans {s t u : BitRAMState} (h : InitFrame s t) (k : InitFrame t u) : InitFrame s u :=
  ⟨k.inputHead.trans h.inputHead, k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun j hj h37 h322 h329 => (k.tapes j hj h37 h322 h329).trans (h.tapes j hj h37 h322 h329)⟩

def initRowCode : Code := .seq writeCode (BankArray.incrementCode 322)

/-- Initialize one actual array slot to the fraction zero over one. -/
theorem init_row {n : ℕ} (l : Layout n) (nums dens : Vector (List Bool) n)
    (i : Fin n) (B : ℕ) (hl : l.Sized B) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Descriptors.Ready s.val) (h37 : Blank s.val 37) (hd : Stored l nums dens s.val)
    (hindex : BankArray.Word s.val 322 index) (h0 : Word s.val 276 0) (h1 : Word s.val 277 1) :
    ∃ cost t, cost ≤ 81000*(B+2)^2 ∧ Executes input tape initRowCode cost s t ∧
      Descriptors.Ready t.val ∧ Blank t.val 37 ∧
      Stored l (nums.set i (FixedWidth.bits (addressValue l.width) (0 : ℕ).bits))
        (dens.set i (FixedWidth.bits (addressValue l.width) (1 : ℕ).bits)) t.val ∧
      BankArray.Word t.val 322 (Increment.bits index) ∧
      t.val.tapes 329 = s.val.tapes 329 ∧ InitFrame s.val t.val ∧ Outside l s.val t.val := by
  obtain ⟨wc, a, hwc, ew, ha, ha37, had, ham, fa⟩ := write l nums dens i 0 1 B hl
    (by simp) (by simpa using Nat.succ_le_iff.mpr l.width_positive) input tape index hi hil s hs h37 hd hindex h0 h1
  have hai : BankArray.Word a.val 322 index :=
    BankArray.word_of_eq (fa.2.2.2.1 322 (by omega) (by decide)) hindex
  obtain ⟨ic, t, hic, ei, hti, _, htm, _, keep, fi⟩ := BankArray.increment_bank
    322 (by decide) input tape index a hai ha.scratch
  have frame : InitFrame s.val t.val :=
    ⟨fi.1.trans fa.1, fi.2.1.trans fa.2.1, fi.2.2.1.trans fa.2.2.1,
      fun j hj h37 h322 _ => (keep j h322).trans (fa.2.2.2.1 j hj h37)⟩
  refine ⟨wc+ic, t, ?_, ew.seq ei,
    (fun j hj => blank_of_eq (keep j (by omega)) (ha j hj)),
    blank_of_eq (keep 37 (by decide)) ha37, ?_, hti,
    (keep 329 (by decide)).trans (fa.2.2.2.1 329 (by omega) (by decide)), frame,
    (Outside.of_write l i 0 1 ham).trans (Outside.of_memory l htm)⟩
  · nlinarith
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide)) had.width,
      BankArray.word_of_eq (keep 301 (by decide)) had.clock,
      BankArray.word_of_eq (keep 320 (by decide)) had.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) had.denBase, ?_, ?_⟩
    · simpa only [htm] using had.nums
    · simpa only [htm] using had.dens

end Maxwell.Cost.PhysicalMaterial.Dense
