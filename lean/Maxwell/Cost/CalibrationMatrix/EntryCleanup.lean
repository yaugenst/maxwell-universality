import Maxwell.Cost.BankArray.Common
import Maxwell.Cost.CalibrationMatrix.EntryPrepared
import Maxwell.Cost.CalibrationMatrix.WordMove

/-! Reusable division workspace: export four digits and erase the radix. -/
namespace Maxwell.Cost.CalibrationMatrix.Entry
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

def exportChanges (base : ℕ) : Finset ℕ := {1, 3, 70, 71, 72, base, base + 1, base + 2, base + 3}

def exportCode (base : ℕ) : Code :=
  .seq (.call (Rewind.program 3))
    (.seq (.call (WordTransfer.move 3 base))
      (.seq (.call (WordTransfer.move 72 (base + 1)))
        (.seq (.call (WordTransfer.move 71 (base + 2)))
          (.seq (.call (WordTransfer.move 70 (base + 3))) (.call (TapeOps.clear 1))))))

/-- Direction, x, y, z are exported in that order to four consecutive
persistent banks. All division and extraction tapes are blank afterwards. -/
theorem export_digits (base : ℕ) (hbase : 100 ≤ base)
    (input : List Bool) (randomTape : ℕ → Bool) (radix x y z direction : List Bool)
    (s : Store) (hp : Prepared s.val radix direction)
    (hx : BankArray.Word s.val 72 x) (hy : BankArray.Word s.val 71 y) (hz : BankArray.Word s.val 70 z)
    (hblank : ∀ k, k < 4 → Blank s.val (base + k)) :
    ∃ t, Executes input randomTape (exportCode base)
        (16 * direction.length + 12 * (x.length + y.length + z.length) + 6 * radix.length + 54) s t ∧
      BankArray.Word t.val base direction ∧ BankArray.Word t.val (base + 1) x ∧
      BankArray.Word t.val (base + 2) y ∧ BankArray.Word t.val (base + 3) z ∧
      (∀ i, i < 5 → Blank t.val i) ∧ Blank t.val 70 ∧ Blank t.val 71 ∧ Blank t.val 72 ∧
      BinaryPrecision.Frame (exportChanges base) s.val t.val := by
  have hb0 : base ≠ 0 := by omega
  obtain ⟨h0, ⟨ro, hr⟩, h2, ⟨diro, hdir⟩, h4⟩ := hp
  obtain ⟨xo, hx⟩ := hx
  obtain ⟨yo, hy⟩ := hy
  obtain ⟨zo, hz⟩ := hz
  obtain ⟨o0, ho0⟩ := hblank 0 (by decide)
  obtain ⟨o1, ho1⟩ := hblank 1 (by decide)
  obtain ⟨o2, ho2⟩ := hblank 2 (by decide)
  obtain ⟨o3, ho3⟩ := hblank 3 (by decide)
  have scan := WordTransfer.rewind_shifted 3 diro input randomTape direction s.val s.property hdir
  let a := Store.ofState (Rewind.finishAt 3 diro s.val)
  have ea : Executes input randomTape (.call (Rewind.program 3)) (4 * direction.length + 6) s a :=
    .call _ s _ _ scan.1 (by simp [Rewind.program, Rewind.finishAt])
  have atapes : a.val.tapes = Function.update s.val.tapes 3 (BitTape.shifted direction diro) := by
    funext i
    by_cases hi : i = 3
    · subst i; simpa [a, Store.ofState] using scan.2
    · simp [a, Store.ofState, Rewind.finishAt, hi]
  have fa : BinaryPrecision.Frame (exportChanges base) s.val a.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    have hi3 : i ≠ 3 := by simp only [exportChanges, Finset.mem_insert, Finset.mem_singleton, not_or] at hi; tauto
    simp [atapes, hi3]
  obtain ⟨b, eb, btapes, fb, _⟩ := move_word 3 base (by omega) input randomTape direction diro o0 a
    scan.2 (by simpa [Function.update_apply, atapes, show base ≠ 3 by omega] using ho0)
  have fb' : BinaryPrecision.Frame (exportChanges base) a.val b.val := fb.mono (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [exportChanges])
  obtain ⟨c, ec, ctapes, fc, _⟩ := move_word 72 (base + 1) (by omega) input randomTape x xo o1 b
    (by simpa [Function.update_apply, btapes, atapes, show (72 : ℕ) ≠ base by omega] using hx)
    (by simpa [Function.update_apply, btapes, atapes, show base + 1 ≠ 3 by omega] using ho1)
  have fc' : BinaryPrecision.Frame (exportChanges base) b.val c.val := fc.mono (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [exportChanges])
  obtain ⟨d, ed, dtapes, fd, _⟩ := move_word 71 (base + 2) (by omega) input randomTape y yo o2 c
    (by simpa [Function.update_apply, ctapes, btapes, atapes, show (71 : ℕ) ≠ base by omega,
      show (71 : ℕ) ≠ base + 1 by omega] using hy)
    (by simpa [Function.update_apply, ctapes, btapes, atapes, show base + 2 ≠ 72 by omega,
      show base + 2 ≠ 3 by omega] using ho2)
  have fd' : BinaryPrecision.Frame (exportChanges base) c.val d.val := fd.mono (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [exportChanges])
  obtain ⟨e, ee, etapes, fe, _⟩ := move_word 70 (base + 3) (by omega) input randomTape z zo o3 d
    (by simpa [Function.update_apply, dtapes, ctapes, btapes, atapes, show (70 : ℕ) ≠ base by omega,
      show (70 : ℕ) ≠ base + 1 by omega, show (70 : ℕ) ≠ base + 2 by omega] using hz)
    (by simpa [Function.update_apply, dtapes, ctapes, btapes, atapes, hb0, show base + 3 ≠ 71 by omega,
      show base + 3 ≠ 72 by omega, show base + 3 ≠ 3 by omega] using ho3)
  have fe' : BinaryPrecision.Frame (exportChanges base) d.val e.val := fe.mono (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [exportChanges])
  have he1 : e.val.tapes 1 = BitTape.shifted radix ro := by
    simpa [Function.update_apply, etapes, dtapes, ctapes, btapes, atapes, hb0, show (1 : ℕ) ≠ base by omega,
      show (1 : ℕ) ≠ base + 1 by omega, show (1 : ℕ) ≠ base + 2 by omega,
      show (1 : ℕ) ≠ base + 3 by omega] using hr
  obtain ⟨t, et, ttapes, ft⟩ := WordCall.clear 1 input randomTape radix ro e he1
  have ft' : BinaryPrecision.Frame (exportChanges base) e.val t.val := by
    refine ⟨ft.1, ft.2.1, ft.2.2.1, ft.2.2.2.1, ft.2.2.2.2.1, ?_⟩
    intro i hi
    have hi1 : i ≠ 1 := by simp only [exportChanges, Finset.mem_insert, Finset.mem_singleton, not_or] at hi; tauto
    exact ft.2.2.2.2.2.1 i hi1 hi1
  have fall := ((((fa.trans fb').trans fc').trans fd').trans fe').trans ft'
  have outside (i : ℕ) (hi : i = 0 ∨ i = 2 ∨ i = 4) : t.val.tapes i = s.val.tapes i := by
    apply fall.tapes
    simp only [exportChanges, Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  refine ⟨t, ?_, ⟨o0, ?_⟩, ⟨o1, ?_⟩, ⟨o2, ?_⟩, ⟨o3, ?_⟩, ?_,
    ⟨zo + z.length, ?_⟩, ⟨yo + y.length, ?_⟩, ⟨xo + x.length, ?_⟩, fall⟩
  · convert ea.seq (eb.seq (ec.seq (ed.seq (ee.seq et)))) using 1 <;> first | rfl | omega
  · simp [ttapes, etapes, dtapes, ctapes, btapes, show base ≠ 1 by omega,
      show base ≠ 70 by omega, show base ≠ 71 by omega, show base ≠ 72 by omega]
  · simp [ttapes, etapes, dtapes, ctapes, hb0,
      show base + 1 ≠ 70 by omega, show base + 1 ≠ 71 by omega]
  · simp [ttapes, etapes, dtapes, show base + 2 ≠ 1 by omega, show base + 2 ≠ 70 by omega]
  · simp [ttapes, etapes, show base + 3 ≠ 1 by omega]
  · intro i hi
    interval_cases i
    · exact RationalAccumulator.blank_of_eq (outside 0 (by simp)) h0
    · exact ⟨ro + radix.length, by simp [ttapes]⟩
    · exact RationalAccumulator.blank_of_eq (outside 2 (by simp)) h2
    · exact ⟨diro + direction.length, by
        simp [ttapes, etapes, dtapes, ctapes, btapes, hb0, show (3 : ℕ) ≠ base by omega,
          show (3 : ℕ) ≠ base + 1 by omega, show (3 : ℕ) ≠ base + 2 by omega]⟩
    · exact RationalAccumulator.blank_of_eq (outside 4 (by simp)) h4
  · simp [ttapes, etapes, show (70 : ℕ) ≠ base + 3 by omega]
  · simp [ttapes, etapes, dtapes, show (71 : ℕ) ≠ base + 3 by omega,
      show (71 : ℕ) ≠ base + 2 by omega]
  · simp [ttapes, etapes, dtapes, ctapes, show (72 : ℕ) ≠ base + 3 by omega,
      show (72 : ℕ) ≠ base + 2 by omega, show (72 : ℕ) ≠ base + 1 by omega]

end Maxwell.Cost.CalibrationMatrix.Entry
