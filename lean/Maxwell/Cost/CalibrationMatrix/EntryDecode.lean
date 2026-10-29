import Maxwell.Cost.CalibrationMatrix.EntryCleanup

/-! Complete reusable radix decoder from persistent input banks. -/
namespace Maxwell.Cost.CalibrationMatrix.Entry
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def decodeChanges (base : ℕ) : Finset ℕ := {0, 2, 4} ∪ exportChanges base

def decodeCode (radixBank indexBank base : ℕ) : Code :=
  .seq (prepareCode radixBank indexBank) (.seq cubeCode (exportCode base))

theorem decode_digits (radixBank indexBank base : ℕ)
    (hrb : 100 ≤ radixBank) (hib : 100 ≤ indexBank) (hbase : 100 ≤ base)
    (input : List Bool) (tape : ℕ → Bool) (radix index : List Bool)
    (hrpos : 0 < addressValue radix) (s : Store)
    (hr : BankArray.Word s.val radixBank radix) (hi : BankArray.Word s.val indexBank index)
    (hblank : ∀ k, k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ (base ≤ k ∧ k < base + 4) → Blank s.val k) :
    ∃ cost t x y z direction,
      cost ≤ 2000 * (radix.length + index.length + 3) ^ 2 ∧
      Executes input tape (decodeCode radixBank indexBank base) cost s t ∧
      BankArray.Word t.val base direction ∧ BankArray.Word t.val (base + 1) x ∧
      BankArray.Word t.val (base + 2) y ∧ BankArray.Word t.val (base + 3) z ∧
      addressValue direction = addressValue index / addressValue radix / addressValue radix / addressValue radix ∧
      addressValue x = addressValue index / addressValue radix / addressValue radix % addressValue radix ∧
      addressValue y = addressValue index / addressValue radix % addressValue radix ∧
      addressValue z = addressValue index % addressValue radix ∧
      direction.length = index.length ∧
      x.length ≤ radix.length + index.length ∧ y.length ≤ radix.length + index.length ∧
      z.length ≤ radix.length + index.length ∧
      (∀ k, k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 → Blank t.val k) ∧
      BinaryPrecision.Frame (decodeChanges base) s.val t.val := by
  obtain ⟨ro, hr⟩ := hr
  obtain ⟨io, hi⟩ := hi
  obtain ⟨a, ea, ha, fa⟩ := prepare radixBank indexBank (by omega) (by omega)
    input tape radix index ro io s hr hi (fun k hk => hblank k (Or.inl hk))
  have ablank (k : ℕ) (hk : 5 ≤ k)
      (hb : k = 70 ∨ k = 71 ∨ k = 72 ∨ (base ≤ k ∧ k < base + 4)) : Blank a.val k :=
    blank_of_eq (fa.tapes k (by simp; omega)) (hblank k (Or.inr hb))
  obtain ⟨cc, b, x, y, z, direction, hcc, ec, hb, hz, hy, hx, hzv, hyv, hxv, hdv,
    hdl, _, _, hxl, hyl, hzl, fc⟩ := cube_digits input tape radix index hrpos a ha
      (ablank 70 (by decide) (by simp)) (ablank 71 (by decide) (by simp))
      (ablank 72 (by decide) (by simp))
  have bblank (k : ℕ) (hk : k < 4) : Blank b.val (base + k) :=
    blank_of_eq (fc.2.2.2.2.2.1 (base + k) (by omega) (by omega) (by omega) (by omega))
      (ablank (base + k) (by omega) (Or.inr (Or.inr (Or.inr (by omega)))))
  obtain ⟨t, et, htd, htx, hty, htz, hsmall, ht70, ht71, ht72, ft⟩ :=
    export_digits base hbase input tape radix x y z direction b hb hx hy hz bblank
  have fa' : BinaryPrecision.Frame (decodeChanges base) s.val a.val := fa.mono (by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [decodeChanges, exportChanges])
  have fc' : BinaryPrecision.Frame (decodeChanges base) a.val b.val := by
    refine ⟨fc.1, fc.2.1, fc.2.2.1, fc.2.2.2.1, fc.2.2.2.2.1, ?_⟩
    intro k hk
    simp only [decodeChanges, exportChanges, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hk
    apply fc.2.2.2.2.2.1 k <;> omega
  have ft' : BinaryPrecision.Frame (decodeChanges base) b.val t.val := ft.mono (Finset.subset_union_right)
  refine ⟨15 * radix.length + 20 * index.length + 38 +
      (cc + (16 * direction.length + 12 * (x.length + y.length + z.length) + 6 * radix.length + 54)),
    t, x, y, z, direction, ?_, ea.seq (ec.seq et), htd, htx, hty, htz,
    hdv, hxv, hyv, hzv, hdl, hxl, hyl, hzl, ?_, (fa'.trans fc').trans ft'⟩
  · rw [hdl]
    nlinarith
  · intro k hk
    rcases hk with hk | rfl | rfl | rfl
    · exact hsmall k hk
    · exact ht70
    · exact ht71
    · exact ht72

end Maxwell.Cost.CalibrationMatrix.Entry
