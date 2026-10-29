import Maxwell.Cost.CalibrationMatrix.PadWord
import Maxwell.Cost.BinaryPrecision

/-! A finite machine appending a fixed-width field from a stored word. -/
namespace Maxwell.Cost.PhysicalMaterial
open Structured RationalAccumulator

/-- Padding and transfer both use physical tape instructions. -/
def fieldCode (source clock work key : ℕ) : Code :=
  .seq (CalibrationMatrix.padWordCode source clock work)
    (.call (TapeOps.copyClear work key))

/-- Append a bounded field, restore both inputs, and reclaim its temporary tape. -/
theorem append_field (source clock work key : ℕ)
    (hsc : source ≠ clock) (hsw : source ≠ work) (hcw : clock ≠ work)
    (hwk : work ≠ key) (input : List Bool) (tape : ℕ → Bool)
    (width : ℕ) (clockWord xs preceding : List Bool)
    (hwidth : clockWord.length = width) (hfit : xs.length ≤ width)
    (so co wo ko : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted xs so)
    (hc : s.val.tapes clock = BitTape.shifted clockWord co)
    (hw : s.val.tapes work = {BitTape.blank with head := wo})
    (hk : s.val.tapes key = BitTape.shiftedEnd preceding ko) :
    ∃ cost t, cost ≤ 28 * width + 16 ∧
      Executes input tape (fieldCode source clock work key) cost s t ∧
      t.val.tapes key = BitTape.shiftedEnd (preceding ++ FixedWidth.bits width xs) ko ∧
      Blank t.val work ∧ BinaryPrecision.Frame {work, key} s.val t.val := by
  obtain ⟨pc, a, hpc, ep, haw, _, _, _, fp⟩ := CalibrationMatrix.pad_word
    source clock work hsc hsw hcw input tape width clockWord xs hwidth hfit
    so co wo s hs hc hw
  have hak : a.val.tapes key = BitTape.shiftedEnd preceding ko :=
    (fp.tapes key hwk.symm).trans hk
  obtain ⟨result, et, hp, htw, htk, ft⟩ := TapeOps.copyClear_shifted_steps work key hwk
    input tape (FixedWidth.bits width xs) preceding wo ko a.val a.property haw hak
  let t := Store.ofState result
  have ec : Executes input tape (.call (TapeOps.copyClear work key))
      (8 * (FixedWidth.bits width xs).length + 4) a t :=
    .call _ a result _ et (by rw [hp]; rfl)
  have fpad : BinaryPrecision.Frame {work, key} s.val a.val := by
    refine ⟨fp.address, fp.inputHead, fp.memory, fp.randomCursor, fp.output, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact fp.tapes i hi.1
  have ftransfer : BinaryPrecision.Frame {work, key} a.val t.val := by
    refine ⟨ft.1, ft.2.1, ft.2.2.1, ft.2.2.2.1, ft.2.2.2.2.1, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact ft.2.2.2.2.2.1 i hi.1 hi.2
  refine ⟨pc + (8 * (FixedWidth.bits width xs).length + 4), t, ?_, ep.seq ec,
    htk, ⟨wo + (FixedWidth.bits width xs).length, htw⟩, fpad.trans ftransfer⟩
  rw [FixedWidth.bits_length]
  omega

end Maxwell.Cost.PhysicalMaterial
