import Maxwell.Cost.PhysicalMaterial.Field
import Maxwell.Cost.CalibrationMatrix.Residue
import Maxwell.Cost.CalibrationMatrix.TableKey

namespace Maxwell.Cost.PhysicalMaterial
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def keyWork : Finset ℕ := {0, 1, 2, 3, 4, 244, 247, 248}

def coordinateCode (source : ℕ) : Code :=
  .seq (CalibrationMatrix.Residue.code 243 source 244)
    (.seq (fieldCode 244 249 248 247) (.call (TapeOps.clear 244)))

/-- A coordinate is read from its actual canonical input word, reduced modulo
20 by long division, and appended as five physical key bits. -/
theorem append_coordinate (source : ℕ) (hsource : 240 ≤ source ∧ source ≤ 242)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (preceding : List Bool)
    (origin : ℤ) (s : Store) (hn : Word s.val source n)
    (hperiod : Word s.val 243 20) (hclock : Word s.val 249 16)
    (hblank : ∀ i, i < 5 → Blank s.val i)
    (h244 : Blank s.val 244) (h248 : Blank s.val 248)
    (hkey : s.val.tapes 247 = BitTape.shiftedEnd preceding origin) :
    ∃ cost t, cost ≤ 700 * (n.bits.length + 8)^2 + 190 ∧
      Executes input tape (coordinateCode source) cost s t ∧
      t.val.tapes 247 = BitTape.shiftedEnd
        (preceding ++ CalibrationMatrix.TableKey.field 5 (n % 20)) origin ∧
      (∀ i, i < 5 → Blank t.val i) ∧ Blank t.val 244 ∧ Blank t.val 248 ∧
      BinaryPrecision.Frame keyWork s.val t.val := by
  obtain ⟨rc, a, hrc, er, har, hsize, ha0, fr⟩ := CalibrationMatrix.Residue.executes
    243 source 244 (by decide) (by omega) (by decide) input tape n.bits s hperiod hn h244 hblank
  rw [addressValue_bits] at har hsize
  obtain ⟨ro, hro⟩ := har
  obtain ⟨co, hco⟩ := hclock
  obtain ⟨wo, hwo⟩ := h248
  have hak : a.val.tapes 247 = BitTape.shiftedEnd preceding origin :=
    (fr.tapes 247 (by decide)).trans hkey
  have hac : a.val.tapes 249 = BitTape.shifted (16 : ℕ).bits co :=
    (fr.tapes 249 (by decide)).trans hco
  have haw : a.val.tapes 248 = {BitTape.blank with head := wo} :=
    (fr.tapes 248 (by decide)).trans hwo
  obtain ⟨fc, b, hfc, ef, hbk, hbw, ff⟩ := append_field 244 249 248 247
    (by decide) (by decide) (by decide) (by decide) input tape 5 (16 : ℕ).bits
    (n % 20).bits preceding (by decide) (by simpa only [Nat.size_eq_bits_len] using hsize)
    ro co wo origin a hro hac haw hak
  have hbr : b.val.tapes 244 = BitTape.shifted (n % 20).bits ro :=
    (ff.tapes 244 (by decide)).trans hro
  obtain ⟨t, ec, htapes, ft⟩ := WordCall.clear 244 input tape (n % 20).bits ro b hbr
  have fclear : BinaryPrecision.Frame keyWork b.val t.val := by
    refine ⟨ft.1, ft.2.1, ft.2.2.1, ft.2.2.2.1, ft.2.2.2.2.1, ?_⟩
    intro i hi
    have hi244 : i ≠ 244 := by intro he; subst i; exact hi (by simp [keyWork])
    simp only [htapes, Function.update_of_ne hi244]
  have fall : BinaryPrecision.Frame keyWork s.val t.val :=
    ((fr.mono (by simp [CalibrationMatrix.Residue.changes, keyWork])).trans
      (ff.mono (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi; rcases hi with rfl | rfl <;> simp [keyWork]))).trans fclear
  refine ⟨rc + (fc + (6 * (n % 20).bits.length + 4)), t, ?_,
    er.seq (ef.seq ec), ?_, ?_, ⟨ro + (n % 20).bits.length, ?_⟩, ?_, fall⟩
  · rw [Nat.size_eq_bits_len]
    omega
  · simpa [htapes, CalibrationMatrix.TableKey.field] using hbk
  · intro i hi
    exact blank_of_eq ((show t.val.tapes i = b.val.tapes i by simp [htapes, show i ≠ 244 by omega]).trans
      (ff.tapes i (by simp; omega))) (ha0 i hi)
  · simp [htapes]
  · exact blank_of_eq (by simp [htapes]) hbw

end Maxwell.Cost.PhysicalMaterial
