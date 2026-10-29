import Maxwell.Cost.RationalCompare
import Maxwell.Cost.RationalAccumulator.Reset

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

def replaced (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 30 (v 32)) 31 (v 33)

def selected (v : ℕ → ℕ) : ℕ → ℕ :=
  if (v 30 : ℚ) / v 31 < (v 32 : ℚ) / v 33 then replaced v else v

def updated (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (selected v) 32 0) 33 0

def replaceCode : Code :=
  .seq (.call (TapeOps.clear 30))
    (.seq (.call (TapeOps.clear 31))
      (.seq (.call (WordTransfer.clone 32 30)) (.call (WordTransfer.clone 33 31))))

def clearCandidatesCode : Code :=
  .seq (.call (TapeOps.clear 32)) (.call (TapeOps.clear 33))

def updateCode : Code :=
  .seq RationalCompare.code (.seq (.branch 35 replaceCode .skip) clearCandidatesCode)

/-- Replace the stored maximum by the candidate words themselves. The
computed cross-products are never retained as the maximum representation. -/
theorem replace (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape replaceCode
      (6*((v 30).bits.length+(v 31).bits.length) +
        15*((v 32).bits.length+(v 33).bits.length)+42) s t ∧
      Bank t.val (replaced v) ∧ Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ha, hab, har, haf⟩ := clear_bank 30 (by decide) (by decide) input tape v 0 s hbank hready
  let v1 := Function.update v 30 0
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clear_bank 31 (by decide) (by decide) input tape v1 0 a hab har
  let v2 := Function.update v1 31 0
  obtain ⟨c, hc, hcb, hcr, hcf⟩ := clone_bank 32 30 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v2 0 b hbb (by simp [v2, v1]) hbr
  let v3 := Function.update v2 30 (v2 32)
  obtain ⟨d, hd, hdb, hdr, hdf⟩ := clone_bank 33 31 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v3 0 c hcb (by simp [v3, v2, v1]) hcr
  have hv : Function.update v3 31 (v3 33) = replaced v := by
    funext i
    by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;>
      simp [h30, h31, v3, v2, v1, replaced]
  refine ⟨d, ?_, hv ▸ hdb, hdr, ((haf.trans hbf).trans hcf).trans hdf⟩
  have he := ha.seq (hb.seq (hc.seq hd))
  convert he using 1
  · simp [replaceCode]
  · simp only [v1, v2, v3,
      Function.update_of_ne (show 31 ≠ 30 by decide),
      Function.update_of_ne (show 32 ≠ 30 by decide),
      Function.update_of_ne (show 32 ≠ 31 by decide),
      Function.update_of_ne (show 33 ≠ 30 by decide),
      Function.update_of_ne (show 33 ≠ 31 by decide)]
    omega

theorem clear_candidates (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape clearCandidatesCode
      (6*((v 32).bits.length+(v 33).bits.length)+8) s t ∧
      Bank t.val (Function.update (Function.update v 32 0) 33 0) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ha, hab, har, haf⟩ := clear_bank 32 (by decide) (by decide) input tape v 0 s hbank hready
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clear_bank 33 (by decide) (by decide)
    input tape (Function.update v 32 0) 0 a hab har
  refine ⟨b, ?_, hbb, hbr, haf.trans hbf⟩
  convert ha.seq hb using 1
  · rfl
  · simp only [Function.update_of_ne (show 33 ≠ 32 by decide)]
    omega

theorem selected_candidate (v : ℕ → ℕ) (i : ℕ) (h : i = 32 ∨ i = 33) :
    selected v i = v i := by
  rcases h with rfl | rfl <;> unfold selected <;> split_ifs <;> simp [replaced]

theorem selected_bound (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 33 → (v i).bits.length ≤ B) :
    ∀ i, 30 ≤ i → i ≤ 33 → (selected v i).bits.length ≤ B := by
  intro i hi hi'
  unfold selected
  split_ifs
  · by_cases h30 : i = 30
    · subst i; simpa [replaced] using hbits 32 (by decide) (by decide)
    · by_cases h31 : i = 31
      · subst i; simpa [replaced] using hbits 33 (by decide) (by decide)
      · simpa [replaced, h30, h31] using hbits i hi hi'
  · exact hbits i hi hi'

/-- Actual comparison, data-dependent finite branch, exact selected-word
copy and cleanup. The same bounded-width bank is ready for the next input. -/
theorem update (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 33 → (v i).bits.length ≤ B)
    (hA : 0 < v 31) (hB : 0 < v 33) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 9000 * (B + 2)^2 ∧
      Executes input tape updateCode cost s t ∧
      Bank t.val (updated v) ∧ Scratch t.val 0 ∧ RationalCompare.Frame s.val t.val := by
  obtain ⟨c, a, hc, ha, haflag, hab, har, haf⟩ :=
    RationalCompare.compare input tape v B hbits hA hB h35 h36 s hbank hready
  have hselect : ∃ d, ∃ b : Store, d ≤ 42 * B + 43 ∧
      Executes input tape (.branch 35 replaceCode .skip) d a b ∧
      Bank b.val (selected v) ∧ Scratch b.val 0 ∧ RationalCompare.Frame a.val b.val := by
    by_cases hlt : (v 30 : ℚ) / v 31 < (v 32 : ℚ) / v 33
    · obtain ⟨b, hb, hbb, hbr, hbf⟩ := replace input tape v a hab har
      refine ⟨_, b, ?_, Executes.yes (by simpa [hlt] using haflag) hb,
        by simpa [selected, hlt] using hbb, hbr, RationalCompare.frame_of_bank hbf⟩
      have h30 := hbits 30 (by decide) (by decide)
      have h31 := hbits 31 (by decide) (by decide)
      have h32 := hbits 32 (by decide) (by decide)
      have h33 := hbits 33 (by decide) (by decide)
      omega
    · exact ⟨2, a, by omega, Executes.no (by simpa [hlt] using haflag) (Executes.skip a),
        by simpa [selected, hlt] using hab, har, by simp [RationalCompare.Frame]⟩
  obtain ⟨d, b, hd, hb, hbb, hbr, hbf⟩ := hselect
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_candidates input tape (selected v) b hbb hbr
  refine ⟨c + (d + (6*((selected v 32).bits.length+(selected v 33).bits.length)+8)), t,
    ?_, ha.seq (hb.seq ht), htb, htr, (haf.trans hbf).trans (RationalCompare.frame_of_bank htf)⟩
  have h32 := selected_bound v B hbits 32 (by decide) (by decide)
  have h33 := selected_bound v B hbits 33 (by decide) (by decide)
  nlinarith

/-- The selected numerator/denominator are an input pair, so repeated
comparisons cannot enlarge the stored rational representation. -/
theorem updated_pair (v : ℕ → ℕ) :
    (updated v 30, updated v 31) = (v 30, v 31) ∨
      (updated v 30, updated v 31) = (v 32, v 33) := by
  unfold updated selected
  split_ifs <;> simp [replaced]

theorem updated_value (v : ℕ → ℕ) :
    (updated v 30 : ℚ) / updated v 31 = max ((v 30 : ℚ) / v 31) ((v 32 : ℚ) / v 33) := by
  unfold updated selected
  split_ifs with h
  · simpa [replaced] using (max_eq_right h.le).symm
  · simpa using (max_eq_left (le_of_not_gt h)).symm

end Maxwell.Cost.MagnitudeMax
