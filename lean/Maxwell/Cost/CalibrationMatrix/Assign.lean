import Maxwell.Cost.WordCall
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.CalibrationMatrix.Assign
open Structured

def code (source target : ℕ) : Code := .seq (.call (TapeOps.clear target)) (.call (WordTransfer.clone source target))

/-- Replace one descriptor by a physical copy, charging both its old-word
cleanup and its new-word copy. The source is restored at its original head. -/
theorem executes (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs old : List Bool) (s : Store)
    (hs : BankArray.Word s.val source xs) (ht : BankArray.Word s.val target old) :
    ∃ t, Executes input tape (code source target) (6*old.length+4+(15*xs.length+17)) s t ∧
      BankArray.Word t.val target xs ∧
      (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) ∧
      WordTransfer.Frame target target s.val t.val := by
  obtain ⟨so, hs⟩ := hs
  obtain ⟨targetOrigin, ht⟩ := ht
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear target input tape old targetOrigin s ht
  obtain ⟨t, et, htapes, ft⟩ := WordCall.clone source target hne input tape xs so (targetOrigin+old.length) a
    (by simpa [ha, hne] using hs) (by simp [ha])
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by simp [htapes, ha, hi]
  exact ⟨t, ea.seq et, ⟨targetOrigin+old.length, by simp [htapes]⟩, keep,
    ft.1.trans fa.1, ft.2.1.trans fa.2.1, ft.2.2.1.trans fa.2.2.1,
    ft.2.2.2.1.trans fa.2.2.2.1, ft.2.2.2.2.1.trans fa.2.2.2.2.1,
    (fun i hi _ => keep i hi),
    fun i h24 h25 h26 h27 => (ft.2.2.2.2.2.2 i h24 h25 h26 h27).trans (fa.2.2.2.2.2.2 i h26 h27)⟩

end Maxwell.Cost.CalibrationMatrix.Assign
