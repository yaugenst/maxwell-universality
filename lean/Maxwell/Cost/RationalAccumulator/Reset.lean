import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.RationalAccumulator

open Structured

theorem clear_bank (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ t : Store, Executes input tape (.call (TapeOps.clear target))
      (6 * (v target).bits.length + 4) s t ∧
      Bank t.val (Function.update v target 0) ∧ Scratch t.val scalar ∧ Frame s.val t.val := by
  obtain ⟨origin, hword⟩ := hbank target ht ht'
  obtain ⟨t, he, hp, hclear, hf⟩ := TapeOps.clear_steps target input tape (v target).bits origin
    s.val s.property hword
  refine ⟨Store.ofState t, Executes.call _ _ _ _ he (by simp [TapeOps.clear, hp]), ?_, ?_,
    clone_frame (Or.inr ⟨ht, ht'⟩) (Or.inr ⟨ht, ht'⟩) (WordTransfer.frame_of_copy hf)⟩
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      simp only [Function.update_self, zero_word_iff_blank]
      exact ⟨origin + (v target).bits.length, hclear⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.2.2.2.2.2.1 i hit hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      word_of_eq (hf.2.2.2.2.2.1 1 (by omega) (by omega)) hready.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩

def resetCode : Code :=
  .seq (.call (TapeOps.clear 30)) (.seq (.call (TapeOps.clear 31)) (.call (TapeOps.clear 32)))

def resetBank (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update v 30 0) 31 0) 32 0

theorem reset (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape resetCode
      (6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length)+12) s t ∧
      Bank t.val (resetBank v) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨a, ha, hab, har, haf⟩ := clear_bank 30 (by decide) (by decide) input tape v 0 s hbank hready
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clear_bank 31 (by decide) (by decide) input tape
    (Function.update v 30 0) 0 a hab har
  obtain ⟨c, hc, hcb, hcr, hcf⟩ := clear_bank 32 (by decide) (by decide) input tape
    (Function.update (Function.update v 30 0) 31 0) 0 b hbb hbr
  refine ⟨c, ?_, hcb, hcr, (haf.trans hbf).trans hcf⟩
  have he := Executes.seq ha (Executes.seq hb hc)
  simp only [Function.update_of_ne (show 31 ≠ 30 by decide),
    Function.update_of_ne (show 32 ≠ 31 by decide), Function.update_of_ne (show 32 ≠ 30 by decide)] at he
  have hcost : 6*(v 30).bits.length+4 + (6*(v 31).bits.length+4 + (6*(v 32).bits.length+4)) =
      6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length)+12 := by omega
  simpa only [hcost, resetCode] using he

end Maxwell.Cost.RationalAccumulator
