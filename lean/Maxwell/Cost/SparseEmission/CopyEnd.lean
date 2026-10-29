import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.ScanForward

namespace Maxwell.Cost.SparseEmission.CopyEnd
open Structured
open SourceCircuit (Frame)

def code (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source target)) (.call (ScanForward.program target))

theorem executes (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool) (origin : ℤ)
    (s : Store) (hs : s.val.tapes source = BitTape.shifted word origin)
    (ht : s.val.tapes target = BitTape.blank) :
    ∃ t, Executes input randomTape (code source target) (20*word.length+21) s t ∧
      t.val.tapes target = BitTape.atEnd word ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame {target} s.val t.val ∧ (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone source target hne input randomTape word origin 0 s hs
    (by simpa [BitTape.blank] using ht)
  have aw : a.val.tapes target = BitTape.shifted word 0 := by simp [atapes]
  obtain ⟨es,sw,sf⟩ := ScanForward.shifted_steps target 0 input randomTape word a.val a.property aw
  let t := Store.ofState (ScanForward.finish target word.length a.val)
  have e2 : Executes input randomTape (.call (ScanForward.program target)) (5*word.length+4) a t :=
    .call _ a _ _ es (by simp [ScanForward.program,ScanForward.finish])
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by
    simp [t,Store.ofState,ScanForward.finish,atapes,hi]
  have cf : Frame {target} s.val a.val := SourceCircuit.frame_transfer af (by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [atapes,hi])
  have tf : Frame {target} a.val t.val := by
    refine ⟨sf.2.1,sf.2.2.2.1,sf.2.2.2.2.1,?_,?_,?_⟩
    · intro i _ hi
      simp only [Finset.mem_singleton] at hi
      exact sf.2.2.2.2.2.1 i hi hi
    · exact sf.2.2.2.2.2.2 23 (by decide) (by decide)
    · intro i hi
      exact sf.2.2.2.2.2.2 i (by omega) (by omega)
  refine ⟨t,?_,?_,sf.1.trans af.1,sf.2.2.1.trans af.2.2.1,cf.trans tf,keep⟩
  · convert ea.seq e2 using 1 <;> first | rfl | omega
  · simpa [t,Store.ofState,BitTape.shiftedEnd,BitTape.atEnd] using sw

end Maxwell.Cost.SparseEmission.CopyEnd
