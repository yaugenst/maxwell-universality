import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.DecoderTerm
open Structured

def takeEndCode (source target : ℕ) : Code :=
  .seq (.call (Rewind.program source)) (.call (WordTransfer.move source target))

theorem takeEnd (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (so dest : ℤ)
    (s : Store) (hs : s.val.tapes source = BitTape.shiftedEnd bits so)
    (ht : s.val.tapes target = {BitTape.blank with head := dest}) :
    ∃ t : Store, Executes input tape (takeEndCode source target) (16*bits.length+17) s t ∧
      t.val.tapes source = {BitTape.blank with head := so+bits.length} ∧
      t.val.tapes target = BitTape.shifted bits dest ∧ WordTransfer.Frame source target s.val t.val := by
  have hr := WordTransfer.rewind_shifted source so input tape bits s.val s.property hs
  let r := Rewind.finishAt source so s.val
  let rS := Store.ofState r
  have er : Executes input tape (.call (Rewind.program source)) (4*bits.length+6) s rS :=
    .call _ _ _ _ hr.1 rfl
  have fr : WordTransfer.Frame source target s.val rS.val :=
    WordTransfer.frame_rewind source target source (Or.inl rfl) so s.val
  obtain ⟨m,hm,hmp,hms,hmt,hmf⟩ := WordTransfer.move_steps source target hne input tape bits so dest
    rS.val rS.property hr.2 (by simpa [rS, Store.ofState, r, Rewind.finishAt, Ne.symm hne] using ht)
  let mS := Store.ofState m
  have em : Executes input tape (.call (WordTransfer.move source target))
      (12*bits.length+11) rS mS := by
    simpa using Executes.call _ rS m _ hm (by rw [hmp]; rfl)
  refine ⟨mS,?_,hms,hmt,fr.trans hmf⟩
  simpa only [takeEndCode, show 4*bits.length+6+(12*bits.length+11)=16*bits.length+17 by omega]
    using er.seq em

def clearOvershootCode (work : ℕ) : Code :=
  .seq (.call (RewindOvershoot.program work)) (.call (TapeOps.clear work))

theorem clearOvershoot (work : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (distance : ℕ) (hn : 0 < bits.length)
    (hd : bits.length ≤ distance) (s : Store)
    (hw : s.val.tapes work = {BitTape.shifted bits origin with head := origin+distance}) :
    ∃ t : Store, Executes input tape (clearOvershootCode work)
      (4*distance+6*bits.length+11) s t ∧
      t.val.tapes work = {BitTape.blank with head := origin+bits.length} ∧
      WordTransfer.Frame work work s.val t.val := by
  have hr := WordTransfer.rewind_overshoot_shifted work origin input tape bits distance hn hd
    s.val s.property hw
  let r := RewindOvershoot.finish work origin s.val
  let rS := Store.ofState r
  have er : Executes input tape (.call (RewindOvershoot.program work)) (4*distance+7) s rS :=
    .call _ _ _ _ hr.1 rfl
  have fr : WordTransfer.Frame work work s.val rS.val :=
    WordTransfer.frame_rewind work work work (Or.inl rfl) origin s.val
  obtain ⟨c,hc,hcp,hcw,hcf⟩ := TapeOps.clear_steps work input tape bits origin rS.val rS.property hr.2
  let cS := Store.ofState c
  have ec : Executes input tape (.call (TapeOps.clear work)) (6*bits.length+4) rS cS := by
    simpa using Executes.call _ rS c _ hc (by rw [hcp]; rfl)
  refine ⟨cS,?_,hcw,fr.trans (WordTransfer.frame_of_copy hcf)⟩
  simpa only [clearOvershootCode,
    show 4*distance+7+(6*bits.length+4)=4*distance+6*bits.length+11 by omega] using er.seq ec

end Maxwell.Cost.DecoderTerm
