import Maxwell.Cost.WordTransfer
import Maxwell.Cost.TapeReset
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.TakeParsed

open Structured

def code (source target : ℕ) : Code :=
  .seq (.call (Rewind.program source))
    (.seq (.call (Copy.program source target))
      (.seq (.call (TapeReset.program source)) (.call (Rewind.program target))))

theorem steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (targetOrigin : ℤ)
    (s : Store) (hsource : s.val.tapes source = BitTape.atEnd bits)
    (htarget : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t : Store, Executes input tape (code source target) (21 * bits.length + 22) s t ∧
      t.val.tapes source = BitTape.blank ∧
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
  have hcs' : cS.val.tapes source = BitTape.atEnd bits := by
    simpa [cS, Store.ofState, BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hcs
  have he := TapeReset.steps source input tape bits cS.val cS.property hcs'
  let e := TapeReset.finish source cS.val
  let eS := Store.ofState e
  have ee : Executes input tape (.call (TapeReset.program source)) (6*bits.length+6) cS eS :=
    Executes.call _ _ _ _ he (by simp [e, TapeReset.program, TapeReset.finish])
  have hetarget : eS.val.tapes target = BitTape.shiftedEnd bits targetOrigin := by
    simpa [eS, Store.ofState, e, TapeReset.finish, Ne.symm hne, cS] using hct
  have hf := WordTransfer.rewind_shifted target targetOrigin input tape bits eS.val eS.property hetarget
  let f := Rewind.finishAt target targetOrigin eS.val
  let fS := Store.ofState f
  have ef : Executes input tape (.call (Rewind.program target)) (4*bits.length+6) eS fS :=
    Executes.call _ _ _ _ hf.1 (by simp [f, Rewind.program, Rewind.finishAt])
  have hresetframe : WordTransfer.Frame source target cS.val eS.val := by
    have h := TapeReset.finish_frame source cS.val
    rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    exact ⟨ha, hi, hm, hr, ho, fun i his _ => ht i his his,
      fun i _ _ h26 h27 => hg i h26 h27⟩
  refine ⟨fS, ?_, ?_, hf.2,
    (((WordTransfer.frame_rewind source target source (Or.inl rfl) 0 s.val).trans
      (WordTransfer.frame_of_copy hcf)).trans hresetframe).trans
      (WordTransfer.frame_rewind source target target (Or.inr rfl) targetOrigin eS.val)⟩
  · have hexec := Executes.seq er (Executes.seq ec (Executes.seq ee ef))
    have hcost : 4*bits.length+6 + (7*bits.length+4 + (6*bits.length+6 + (4*bits.length+6))) =
        21*bits.length+22 := by omega
    simpa only [hcost, code] using hexec
  · simp [fS, Store.ofState, f, Rewind.finishAt, hne, eS, e, TapeReset.finish]

theorem run (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (targetOrigin : ℤ)
    (s : Store) (hsource : s.val.tapes source = BitTape.atEnd bits)
    (htarget : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t : Store,
      (runPriced ((code source target).compile.next input tape) (21*bits.length+23) s.val).finished =
        some (t.place (code source target).size) ∧
      (runPriced ((code source target).compile.next input tape) (21*bits.length+23) s.val).instructions =
        21*bits.length+22 ∧
      t.val.tapes source = BitTape.blank ∧
      t.val.tapes target = BitTape.shifted bits targetOrigin ∧
      WordTransfer.Frame source target s.val t.val := by
  obtain ⟨t, he, hs, ht, hf⟩ := steps source target hne input tape bits targetOrigin s hsource htarget
  have hr := he.compiled_run (21*bits.length+23) (by omega)
  exact ⟨t, hr.1, hr.2, hs, ht, hf⟩

end Maxwell.Cost.TakeParsed
