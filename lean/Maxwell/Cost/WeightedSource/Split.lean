import Maxwell.Cost.WeightedSource.Round
import Maxwell.Cost.CalibrationMatrix.WriteRow
import Maxwell.Cost.RationalCanonical.Transfer

namespace Maxwell.Cost.WeightedSource.Split
open Structured RationalAccumulator CalibrationMatrix

def positive (z : ℤ) : ℕ := if z<0 then 0 else z.natAbs
def negative (z : ℤ) : ℕ := if z<0 then z.natAbs else 0

theorem value (z : ℤ) : (positive z : ℤ)-negative z=z := by
  by_cases hz : z<0
  · simp [positive,negative,hz,abs_of_neg hz]
  · simp [positive,negative,hz,abs_of_nonneg (by omega : 0≤z)]

def code : Code := .branch 23 (.call (WordTransfer.move 4 31)) (.call (WordTransfer.move 4 30))
def changed : Finset ℕ := {4,30,31}

private theorem move_frame {target : ℕ} {s t : BitRAMState} (ht : target=30 ∨ target=31)
    (hf : WordTransfer.Frame 4 target s t) : BinaryPrecision.Frame changed s t := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  simp only [changed,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact hf.2.2.2.2.2.1 i hi.1 (by omega)

private theorem ready_after {target magnitude : ℕ} {s t : BitRAMState}
    (ht : target=30 ∨ target=31) (hr : Ready s (dotValues 0 0))
    (hw : Word t target magnitude) (hf : WordTransfer.Frame 4 target s t) :
    Ready t (Function.update (dotValues 0 0) target magnitude) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi hj
    by_cases hit : i=target
    · subst i; simpa using hw
    · simpa only [Function.update_of_ne hit] using word_of_eq
        (hf.2.2.2.2.2.1 i (by omega) hit) (hr.1 i hi hj)
  · rcases hr.2.1 with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) h0,
      blank_of_eq (hf.2.2.2.2.2.1 1 (by omega) (by omega)) h1,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) h2,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) h3,
      blank_of_eq (hf.2.2.2.2.2.1 5 (by omega) (by omega)) h5,
      blank_of_eq (hf.2.2.2.2.2.1 6 (by omega) (by omega)) h6,
      blank_of_eq (hf.2.2.2.2.2.1 8 (by omega) (by omega)) h8,
      blank_of_eq (hf.2.2.2.2.2.1 9 (by omega) (by omega)) h9⟩
  · exact blank_of_eq (hf.2.2.2.2.2.1 7 (by omega) (by omega)) hr.2.2

/-- The rounded sign selects an actual tape move into one canonical channel;
the other channel remains zero, including for rounded zero. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (z : ℤ)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (hout : SignedRound.Output s.val z) :
    ∃ t : Store, Executes input tape code (12*z.natAbs.bits.length+12) s t ∧
      Ready t.val (dotValues (positive z) (negative z)) ∧ Blank t.val 4 ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨origin,hw,hsg⟩ := hout
  have h4 : Word s.val 4 z.natAbs := ⟨origin,hw⟩
  by_cases hz : z<0
  · obtain ⟨t,he,hz4,hw31,hf⟩ := RationalCanonical.move_word 4 31 z.natAbs (by decide)
      input tape s h4 (by simpa [dotValues] using hr.1 31 (by decide) (by decide))
    have e := Executes.yes (no := .call (WordTransfer.move 4 30)) (by simpa [hz] using hsg) he
    have r := ready_after (Or.inr rfl) hr hw31 hf
    have hv : Function.update (dotValues 0 0) 31 z.natAbs=dotValues (positive z) (negative z) := by
      funext i; simp [dotValues,positive,negative,hz,Function.update_apply]
    exact ⟨t,by convert e using 1 <;> first | rfl | omega,
      hv ▸ r,(zero_word_iff_blank _ _).mp hz4,move_frame (Or.inr rfl) hf⟩
  · obtain ⟨t,he,hz4,hw30,hf⟩ := RationalCanonical.move_word 4 30 z.natAbs (by decide)
      input tape s h4 (by simpa [dotValues] using hr.1 30 (by decide) (by decide))
    have e := Executes.no (yes := .call (WordTransfer.move 4 31)) (by simpa [hz] using hsg) he
    have r := ready_after (Or.inl rfl) hr hw30 hf
    have hv : Function.update (dotValues 0 0) 30 z.natAbs=dotValues (positive z) (negative z) := by
      funext i
      by_cases h30 : i=30 <;> by_cases h31 : i=31 <;>
        simp_all [dotValues,positive,negative,Function.update_apply]
    exact ⟨t,by convert e using 1 <;> first | rfl | omega,
      hv ▸ r,(zero_word_iff_blank _ _).mp hz4,move_frame (Or.inl rfl) hf⟩

end Maxwell.Cost.WeightedSource.Split
