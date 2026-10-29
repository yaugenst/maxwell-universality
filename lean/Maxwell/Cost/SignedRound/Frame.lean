import Maxwell.Cost.Division.Correctness
import Maxwell.Cost.Division.Frame
import Maxwell.Cost.RationalAccumulator.EmitCleanup
import Maxwell.Cost.Increment
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.SignedRound

open Structured

/-- Only the stated scratch tapes and Boolean registers may change. In
particular the caller's sign register 35 is preserved throughout rounding. -/
def Frame (firstPreservedTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, firstPreservedTape ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → (i < 23 ∨ 29 < i) → i ≠ 36 → t.registers i = s.registers i)

theorem Frame.refl (n : ℕ) (s : BitRAMState) : Frame n s s := by simp [Frame]

theorem Frame.trans {n : ℕ} {s t u : BitRAMState} (h : Frame n s t) (k : Frame n t u) :
    Frame n s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi => (kt i hi).trans (ht i hi),
    fun i hi hj hk => (kg i hi hj hk).trans (hg i hi hj hk)⟩

theorem Frame.mono {n m : ℕ} {s t : BitRAMState} (h : Frame n s t) (hm : n ≤ m) :
    Frame m s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by omega), h.2.2.2.2.2.2⟩

theorem Frame.sign {n : ℕ} {s t : BitRAMState} (h : Frame n s t) :
    t.registers 35 = s.registers 35 := h.2.2.2.2.2.2 35 (by omega) (by omega) (by omega)

theorem frame_of_transfer {n source target : ℕ} {s t : BitRAMState}
    (hs : source < n) (ht : target < n) (h : WordTransfer.Frame source target s t) : Frame n s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, htapes, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi => htapes i (by omega) (by omega),
    fun i _ hi _ => hg i (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_normalize {n workTape : ℕ} {s t : BitRAMState}
    (hw : workTape < n) (h : NormalizeWord.Frame workTape s t) : Frame n s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi => ht i (by omega),
    fun i _ hi _ => hg i (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_increment {n workTape : ℕ} {s t : BitRAMState}
    (hw : workTape < n) (h : Increment.Frame workTape s t) : Frame n s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi => ht i (by omega),
    fun i _ hi _ => hg i (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_difference {s t : BitRAMState} (h : SignedDifference.Frame s t) : Frame 3 s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, ht, fun i hi hj _ => hg i hi
    (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_division {s t : BitRAMState} (h : Division.Frame s t) : Frame 5 s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, _, _, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, ht, fun i hi hj _ => hg i hi
    (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_rewind (n workTape : ℕ) (hw : workTape < n) (origin : ℤ) (s : BitRAMState) :
    Frame n s (Rewind.finishAt workTape origin s) :=
  frame_of_transfer hw hw (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin s)

end Maxwell.Cost.SignedRound
