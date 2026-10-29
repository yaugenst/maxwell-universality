import Maxwell.Cost.DecoderFetch.Cleanup
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.DecoderFetch
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq prepare (.seq ArrayAccess.readCode cleanup)

def costCap (width index clock : List Bool) : ℕ :=
  ArrayAccess.costCap width index [] (addressValue width) +
    40 * (width.length + index.length + clock.length + addressValue width + 3)

/-- The fetch arithmetic and addressing workspace, excluding the sample tape. -/
def Scratch (s : BitRAMState) : Prop :=
  Blank s 0 ∧ Blank s 1 ∧ Blank s 2 ∧ Blank s 3 ∧
  Blank s 5 ∧ Blank s 6 ∧ Blank s 8 ∧ Blank s 9

def Frame (s t : BitRAMState) : Prop := Control s t ∧
  (∀ i, i = 4 ∨ i = 8 ∨ 10 ≤ i → i ≠ 45 → t.tapes i = s.tapes i)

/-- One fixed finite program fetches a parsed message index, using the stored
binary width to calculate its bit address. All temporary words are erased,
and the parsed index is consumed so the next term parser can reuse tape 45. -/
theorem executes_reset {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank cbank outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store)
    (hscratch : Scratch s.val)
    (h64 : s.val.tapes 64 = BitTape.shifted width wbank)
    (h45 : s.val.tapes 45 = BitTape.shifted index ibank)
    (h66 : s.val.tapes 66 = BitTape.shifted clock cbank)
    (harray : BitArray.Represents s.val.memory 0 (addressValue width) words)
    (h7 : s.val.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ cost t, cost ≤ costCap width index clock ∧ Executes input tape code cost s t ∧
      t.val.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      Scratch t.val ∧ Blank t.val 45 ∧
      BitArray.Represents t.val.memory 0 (addressValue width) words ∧ Frame s.val t.val ∧
      t.val.tapes 45 = {BitTape.blank with head := ibank} := by
  rcases hscratch with ⟨⟨ao, h0⟩, ⟨wo, h1⟩, ⟨zo, h2⟩, ⟨yo, h3⟩,
    ⟨io, h5⟩, ⟨co, h6⟩, ⟨bo, h8⟩, ⟨saved, h9⟩⟩
  obtain ⟨p, ep, hp, fp⟩ := prepare_executes input tape width index clock wo io co
    wbank ibank cbank s h1 h5 h6 h64 h45 h66
  have hready : ArrayAccess.Ready p.val width index [] ao wo zo yo io bo saved := by
    constructor
    · simpa [hp] using h0
    · simp [hp]
    · simpa [hp] using h2
    · simpa [hp] using h3
    · simp [hp]
    · simpa [hp, BitTape.shifted, BitTape.blank] using h8
    · simpa [hp] using h9
  obtain ⟨rcost, r, address, addressOrigin, hrc, er, hr5, _, hrl, hr6, hr7, hrm, harr, restored, fr⟩ :=
    ArrayAccess.read_executes input tape width index [] clock words i ao wo zo yo io bo saved co outputOrigin
      hwidth hindex hclock p hready
      (by simpa [fp.2.2.2.1, addressValue] using harray)
      (by simp [hp]) (by simpa [hp] using h7)
  obtain ⟨widthOrigin, hr1⟩ := restored.width
  have hr45 : r.val.tapes 45 = BitTape.shifted index ibank := by
    rw [fr.2.2.2.1 45 (by omega), hp]
    simpa using h45
  obtain ⟨t, et, ht, ft⟩ := cleanup_executes input tape width address clock index
    widthOrigin addressOrigin co ibank r hr1 hr5 hr6 hr45
  have frame : Frame s.val t.val := by
    refine ⟨fp.trans ((Control.of_read fr hrm).trans ft), ?_⟩
    intro j hj hj45
    simp only [ht, Function.update_apply]
    have hj1 : j ≠ 1 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    simp only [hj45, hj6, hj5, hj1, ↓reduceIte]
    rw [fr.2.2.2.1 j hj, hp]
    simp [hj1, hj5, hj6]
  refine ⟨15 * (width.length + index.length + clock.length) + 51 +
      (rcost + (6 * width.length + 10 * address.length + 10 * clock.length + 11 * index.length + 34)),
    t, ?_, ep.seq (er.seq et), ?_, ?_, ?_, ?_, frame, ?_⟩
  · dsimp [costCap]
    simp only [List.length_nil] at hrl
    omega
  · simpa [ht] using hr7
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨o, ho⟩ := restored.zero
      exact ⟨o, by simpa [ht] using ho⟩
    · exact ⟨widthOrigin + width.length, by simp [ht]⟩
    · obtain ⟨o, ho⟩ := restored.scratch
      exact ⟨o, by simpa [ht] using ho⟩
    · exact ⟨yo + index.length, by simpa [ht] using restored.multiply⟩
    · exact ⟨addressOrigin + address.length, by simp [ht]⟩
    · exact ⟨co + clock.length, by simp [ht]⟩
    · exact ⟨bo, by simpa [ht, BitTape.shifted, BitTape.blank] using restored.base⟩
    · exact ⟨saved + width.length, by simpa [ht] using restored.saved⟩
  · exact ⟨ibank, by simp [ht]⟩
  · simpa [ft.2.2.2.1, addressValue] using harr
  · simp [ht]

theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank cbank outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store)
    (hscratch : Scratch s.val)
    (h64 : s.val.tapes 64 = BitTape.shifted width wbank)
    (h45 : s.val.tapes 45 = BitTape.shifted index ibank)
    (h66 : s.val.tapes 66 = BitTape.shifted clock cbank)
    (harray : BitArray.Represents s.val.memory 0 (addressValue width) words)
    (h7 : s.val.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ cost t, cost ≤ costCap width index clock ∧ Executes input tape code cost s t ∧
      t.val.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      Scratch t.val ∧ Blank t.val 45 ∧
      BitArray.Represents t.val.memory 0 (addressValue width) words ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, ht7, hs, hi, harr, hf, _⟩ :=
    executes_reset input tape width index clock words i wbank ibank cbank outputOrigin
      hwidth hindex hclock s hscratch h64 h45 h66 harray h7
  exact ⟨cost, t, hc, he, ht7, hs, hi, harr, hf⟩

set_option maxRecDepth 4096 in
/-- The same uniform finite code runs under its proved cap on every random tape. -/
theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank cbank outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : BitRAMState) (hpc : s.pc = 0)
    (hscratch : Scratch s)
    (h64 : s.tapes 64 = BitTape.shifted width wbank)
    (h45 : s.tapes 45 = BitTape.shifted index ibank)
    (h66 : s.tapes 66 = BitTape.shifted clock cbank)
    (harray : BitArray.Represents s.memory 0 (addressValue width) words)
    (h7 : s.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ t, (runPriced (code.compile.next input tape) (costCap width index clock + 1) s).finished = some t ∧
      (runPriced (code.compile.next input tape) (costCap width index clock + 1) s).instructions ≤
        costCap width index clock ∧
      t.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      Scratch t ∧ Blank t 45 ∧
      BitArray.Represents t.memory 0 (addressValue width) words ∧ Frame s t := by
  obtain ⟨cost, t, hc, he, ht7, hs, hi, harr, hf⟩ :=
    executes input tape width index clock words i wbank ibank cbank outputOrigin
      hwidth hindex hclock ⟨s, hpc⟩ hscratch h64 h45 h66 harray h7
  have hr := he.compiled_run (costCap width index clock + 1) (by omega)
  exact ⟨t.place code.size, hr.1, hr.2.symm ▸ hc, ht7, hs, hi, harr, hf⟩

end Maxwell.Cost.DecoderFetch
