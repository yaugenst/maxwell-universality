import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

/-- Copy a parser's completed word into a bank slot while retaining its
original exact tape for the canonical record logger. -/
def cloneParsedCode (source target : ℕ) : Code :=
  .seq (.call (Rewind.program source))
    (.seq (.call (Copy.program source target)) (.call (Rewind.program target)))

theorem clone_parsed (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (targetOrigin : ℤ)
    (s : Store) (hsource : s.val.tapes source = BitTape.atEnd bits)
    (htarget : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t : Store, Executes input tape (cloneParsedCode source target) (15 * bits.length + 16) s t ∧
      t.val.tapes source = s.val.tapes source ∧
      t.val.tapes target = BitTape.shifted bits targetOrigin ∧
      WordTransfer.Frame source target s.val t.val := by
  have hsource' : s.val.tapes source = BitTape.shiftedEnd bits 0 := by
    simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hsource
  have hr := WordTransfer.rewind_shifted source 0 input tape bits s.val s.property hsource'
  let r := Rewind.finishAt source 0 s.val
  let rS := Store.ofState r
  have er : Executes input tape (.call (Rewind.program source)) (4*bits.length+6) s rS :=
    Executes.call _ _ _ _ hr.1 (by simp [r, Rewind.program, Rewind.finishAt])
  have hrtarget : rS.val.tapes target = {BitTape.blank with head := targetOrigin} := by
    simpa [rS, Store.ofState, r, Rewind.finishAt, Ne.symm hne] using htarget
  obtain ⟨c, hc, hcp, hcs, hct, hcf⟩ := Copy.shifted_steps source target hne input tape bits
    0 targetOrigin rS.val rS.property hr.2 hrtarget
  let cS := Store.ofState c
  have ec : Executes input tape (.call (Copy.program source target)) (7*bits.length+4) rS cS :=
    Executes.call _ _ _ _ hc (by simp [Copy.program, hcp])
  have hf := WordTransfer.rewind_shifted target targetOrigin input tape bits cS.val cS.property hct
  let f := Rewind.finishAt target targetOrigin cS.val
  let fS := Store.ofState f
  have ef : Executes input tape (.call (Rewind.program target)) (4*bits.length+6) cS fS :=
    Executes.call _ _ _ _ hf.1 (by simp [f, Rewind.program, Rewind.finishAt])
  refine ⟨fS, ?_, ?_, hf.2,
    ((WordTransfer.frame_rewind source target source (Or.inl rfl) 0 s.val).trans
      (WordTransfer.frame_of_copy hcf)).trans
      (WordTransfer.frame_rewind source target target (Or.inr rfl) targetOrigin cS.val)⟩
  · convert er.seq (ec.seq ef) using 1
    · rfl
    · omega
  · simpa [fS, Store.ofState, f, Rewind.finishAt, hne, cS, hsource,
      BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hcs

theorem clone_parsed_bank (source target : ℕ) (hs : source = 12 ∨ source = 13)
    (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (n : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v target = 0)
    (hword : s.val.tapes source = BitTape.atEnd n.bits) :
    ∃ t : Store, Executes input tape (cloneParsedCode source target) (15*n.bits.length+16) s t ∧
      Bank t.val (Function.update v target n) ∧ Scratch t.val 0 ∧
      RationalAccumulator.Frame s.val t.val := by
  have htarget := hbank target ht ht'
  rw [hzero, zero_word_iff_blank] at htarget
  obtain ⟨origin, ho⟩ := htarget
  obtain ⟨t, he, hsource, hout, hf⟩ := clone_parsed source target (by omega)
    input tape n.bits origin s hword ho
  have hunchanged (i : ℕ) (hit : i ≠ target) : t.val.tapes i = s.val.tapes i := by
    by_cases his : i = source
    · subst i; exact hsource
    · exact hf.2.2.2.2.2.1 i his hit
  refine ⟨t, he, ?_, ?_, ?_⟩
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin, by simpa only [Function.update_self] using hout⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hunchanged i hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (hunchanged 0 (by omega)) hready.1,
      word_of_eq (hunchanged 1 (by omega)) hready.2.1,
      blank_of_eq (hunchanged 2 (by omega)) hready.2.2.1,
      blank_of_eq (hunchanged 3 (by omega)) hready.2.2.2⟩
  · exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
      fun i _ h30 => hunchanged i (by omega),
      fun i _ h24 h25 h26 h27 => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

end Maxwell.Cost.MagnitudeMax
