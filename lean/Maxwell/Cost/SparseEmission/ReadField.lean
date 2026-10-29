import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.FixedWidth

namespace Maxwell.Cost.SparseEmission.ReadField
open Structured
open SourceCircuit (Frame)

theorem bits_prefix (word suffix : List Bool) : FixedWidth.bits word.length (word++suffix) = word := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa [FixedWidth.bits] using congrArg (List.cons b) ih

def code (source clock target : ℕ) : Code :=
  .seq (.call (FixedWidth.program source clock target)) (.call (Rewind.program clock))

/-- Copy exactly one fixed-width parent identifier from the actual gate
archive, then restore the physical clock. The unread archive suffix stays. -/
theorem executes (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool)
    (word suffix clockWord : List Bool) (clockOrigin : ℤ) (s : Store)
    (hwidth : clockWord.length = word.length)
    (hc : s.val.tapes clock = BitTape.shifted clockWord clockOrigin)
    (hs : TapeRepresents (s.val.tapes source) (word++suffix))
    (ht : s.val.tapes target = BitTape.blank) :
    ∃ t, Executes input randomTape (code source clock target) (14*word.length+10) s t ∧
      t.val.tapes source = {s.val.tapes source with head := (s.val.tapes source).head+word.length} ∧
      t.val.tapes target = BitTape.atEnd word ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame {source,target} s.val t.val ∧
      (∀ i, i ≠ source → i ≠ target → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,hap,has,hac,haw,haf⟩ := FixedWidth.loop source clock target hsc hst hct
    input randomTape clockWord (word++suffix) s.val s.property
    (hc ▸ BitTape.shifted_represents clockWord clockOrigin) hs
  rw [hwidth,bits_prefix] at haw
  have e1 := Executes.call (FixedWidth.program source clock target) s a _ ea
    (by simp [FixedWidth.program,hap])
  let a' := Store.ofState a
  have haClock : a'.val.tapes clock = BitTape.shiftedEnd clockWord clockOrigin := by
    simpa [a',Store.ofState,hc,BitTape.shiftedEnd,BitTape.shifted] using hac
  have rewind := WordTransfer.rewind_shifted clock clockOrigin input randomTape clockWord
    a'.val a'.property haClock
  let t := Store.ofState (Rewind.finishAt clock clockOrigin a'.val)
  have e2 : Executes input randomTape (.call (Rewind.program clock)) (4*clockWord.length+6) a' t :=
    .call _ a' _ _ rewind.1 (by simp [Rewind.program,Rewind.finishAt])
  have finalClock : t.val.tapes clock = s.val.tapes clock := rewind.2.trans hc.symm
  have keep (i : ℕ) (his : i ≠ source) (hit : i ≠ target) : t.val.tapes i = s.val.tapes i := by
    by_cases hic : i = clock
    · subst i; exact finalClock
    · simpa [t,a',Store.ofState,Rewind.finishAt,hic] using haf.2.2.2.2.2.1 i his hic hit
  refine ⟨t,?_,?_,?_,haf.1,haf.2.2.1,?_,keep⟩
  · unfold code
    convert e1.seq e2 using 1
    omega
  · simpa [t,a',Store.ofState,Rewind.finishAt,hsc,hwidth] using has
  · have hw := haw.blank (origin := 0) (by simpa [BitTape.blank] using ht)
    simpa [t,a',Store.ofState,Rewind.finishAt,hct.symm,BitTape.shiftedEnd,BitTape.atEnd] using hw
  · refine ⟨haf.2.1,haf.2.2.2.1,haf.2.2.2.2.1,?_,?_,?_⟩
    · intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact keep i hi.1 hi.2
    · simpa [t,a',Store.ofState,Rewind.finishAt] using
        haf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)
    · intro i hi
      simpa [t,a',Store.ofState,Rewind.finishAt,show i ≠ 24 by omega,show i ≠ 25 by omega] using
        haf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)

end Maxwell.Cost.SparseEmission.ReadField
