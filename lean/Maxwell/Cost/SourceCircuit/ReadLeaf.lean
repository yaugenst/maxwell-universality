import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.FixedWidth

namespace Maxwell.Cost.SourceCircuit.ReadLeaf
open Structured

def code : Code := .seq (.call (FixedWidth.program 98 93 103)) (.call (Rewind.program 93))

theorem fixedWidth_prefix (word suffix : List Bool) :
    FixedWidth.bits word.length (word ++ suffix) = word := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa [FixedWidth.bits] using congrArg (List.cons b) ih

theorem writes_append {before after : BitTape} {preceding word : List Bool}
    (h : TapeWrites before after word) (hb : before = BitTape.atEnd preceding) :
    after = BitTape.atEnd (preceding ++ word) := by
  have hp : TapeWrites BitTape.blank before preceding := by
    rw [hb]
    refine ⟨by simp [BitTape.atEnd,BitTape.blank],?_⟩
    simpa [BitTape.atEnd,BitTape.ofList,BitTape.blank,BitTape.shifted] using
      (writeCells_blank preceding 0).symm
  simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using
    (hp.trans h).blank (origin := 0) rfl

theorem executes (input : List Bool) (tape : ℕ → Bool)
    (word suffix preceding clock : List Bool) (clockOrigin : ℤ) (s : Store)
    (hlen : clock.length = word.length)
    (hc : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (hs : TapeRepresents (s.val.tapes 98) (word ++ suffix))
    (ht : s.val.tapes 103 = BitTape.atEnd preceding) :
    ∃ t, Executes input tape code (14*word.length+10) s t ∧
      t.val.tapes 98 = {s.val.tapes 98 with head := (s.val.tapes 98).head+word.length} ∧
      t.val.tapes 103 = BitTape.atEnd (preceding ++ word) ∧
      t.val.tapes 93 = s.val.tapes 93 ∧ t.val.memory = s.val.memory ∧
      Frame {98,103} s.val t.val ∧ (∀ j, j ≠ 98 → j ≠ 103 → t.val.tapes j = s.val.tapes j) ∧
      t.val.address = s.val.address := by
  obtain ⟨a,ea,hap,a98,a93,aw,af⟩ := FixedWidth.loop 98 93 103 (by omega) (by omega) (by omega)
    input tape clock (word ++ suffix) s.val s.property
    (hc ▸ BitTape.shifted_represents clock clockOrigin) hs
  have ep : Executes input tape (.call (FixedWidth.program 98 93 103))
      (10*clock.length+4) s (Store.ofState a) :=
    .call _ s a _ ea (by simp [FixedWidth.program,hap])
  have aClock : a.tapes 93 = BitTape.shiftedEnd clock clockOrigin := by
    simpa [hc,BitTape.shifted,BitTape.shiftedEnd] using a93
  have er := WordTransfer.rewind_shifted 93 clockOrigin input tape clock
    (Store.ofState a).val (Store.ofState a).property aClock
  let t := Store.ofState (Rewind.finishAt 93 clockOrigin (Store.ofState a).val)
  have eR : Executes input tape (.call (Rewind.program 93)) (4*clock.length+6) (Store.ofState a) t :=
    .call _ _ _ _ er.1 (by simp [Rewind.program,Rewind.finishAt])
  have keep (j : ℕ) (hj98 : j ≠ 98) (hj103 : j ≠ 103) : t.val.tapes j = s.val.tapes j := by
    by_cases hj93 : j = 93
    · subst j
      exact er.2.trans hc.symm
    · simpa [t,Store.ofState,Rewind.finishAt,hj93] using
        af.2.2.2.2.2.1 j hj98 hj93 hj103
  have aOut : a.tapes 103 = BitTape.atEnd (preceding ++ word) := by
    apply writes_append _ ht
    simpa [hlen,fixedWidth_prefix] using aw
  refine ⟨t,?_,?_,?_,keep 93 (by omega) (by omega),af.2.2.1,
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,
      fun j _ hj => keep j (by intro he; exact hj (by simp [he]))
        (by intro he; exact hj (by simp [he])),?_,?_⟩,keep,af.1⟩
  · convert ep.seq eR using 1 <;> first | rfl | omega
  · simpa [t,Store.ofState,Rewind.finishAt,hlen] using a98
  · simpa [t,Store.ofState,Rewind.finishAt] using aOut
  · simpa [t,Store.ofState,Rewind.finishAt] using af.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    simpa [t,Store.ofState,Rewind.finishAt,show j ≠ 24 by omega,show j ≠ 25 by omega] using
      af.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)

end Maxwell.Cost.SourceCircuit.ReadLeaf
