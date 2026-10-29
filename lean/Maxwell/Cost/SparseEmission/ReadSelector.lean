import Maxwell.Cost.SourceCircuit.WordStack
import Maxwell.Cost.SparseEmission.CopyEnd

namespace Maxwell.Cost.SparseEmission.ReadSelector
open Structured

def code : Code := .seq (SourceCircuit.WordStack.code 105 93 111)
  (.seq (.call (WordTransfer.move 111 112)) (.call (ScanForward.program 112)))
def work : Finset ℕ := {105,111,112}

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (word pre clock : List Bool) (clockOrigin : ℤ) (s : Store)
    (hlen : clock.length = word.length)
    (hs : s.val.tapes 105 = BitTape.atEnd (pre++word))
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank)
    (hc : s.val.tapes 93 = BitTape.shifted clock clockOrigin) :
    ∃ t, Executes input randomTape code (32*word.length+25) s t ∧
      t.val.tapes 105 = BitTape.atEnd pre ∧ t.val.tapes 111 = BitTape.blank ∧
      t.val.tapes 112 = BitTape.atEnd word ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame work s.val t.val ∧
      (∀ i, i ∉ work → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,a105,a111,_,aa,am,af,ak⟩ := SourceCircuit.WordStack.executes 105 93 111
    (by decide) (by decide) (by decide) input randomTape word pre clock 0 clockOrigin s
    hlen hs (by simpa [BitTape.blank] using h111) hc
  obtain ⟨bState,ebSteps,bpc,b111,b112,bf⟩ := WordTransfer.move_steps 111 112 (by decide)
    input randomTape word (0-word.length) 0 a.val a.property a111
    (by simpa [BitTape.blank] using (ak 112 (by decide) (by decide)).trans h112)
  let b := Store.ofState bState
  have eb : Executes input randomTape (.call (WordTransfer.move 111 112)) (12*word.length+11) a b :=
    .call _ _ _ _ ebSteps (by rw [bpc]; rfl)
  obtain ⟨ecSteps,c112,cf⟩ := ScanForward.shifted_steps 112 0 input randomTape word b.val b.property b112
  let t := Store.ofState (ScanForward.finish 112 word.length b.val)
  have ec : Executes input randomTape (.call (ScanForward.program 112)) (5*word.length+4) b t :=
    .call _ _ _ _ ecSteps (by simp [ScanForward.program,ScanForward.finish])
  have tkeep (i : ℕ) (hi : i ≠ 112) : t.val.tapes i = b.val.tapes i :=
    cf.2.2.2.2.2.1 i hi hi
  have keep (i : ℕ) (hi : i ∉ work) : t.val.tapes i = s.val.tapes i := by
    have h105 : i ≠ 105 := by simp_all [work]
    have h111 : i ≠ 111 := by simp_all [work]
    have h112 : i ≠ 112 := by simp_all [work]
    exact ((tkeep i h112).trans (bf.2.2.2.2.2.1 i h111 h112)).trans (ak i h105 h111)
  have bframe : SourceCircuit.Frame work a.val b.val := SourceCircuit.frame_transfer bf (by
    intro i hi
    exact bf.2.2.2.2.2.1 i (by simp_all [work]) (by simp_all [work]))
  have cframe : SourceCircuit.Frame work b.val t.val := by
    refine ⟨cf.2.1,cf.2.2.2.1,cf.2.2.2.2.1,?_,?_,?_⟩
    · intro i _ hi; exact tkeep i (by simp_all [work])
    · exact cf.2.2.2.2.2.2 23 (by decide) (by decide)
    · intro i hi; exact cf.2.2.2.2.2.2 i (by omega) (by omega)
  refine ⟨t,?_,?_,?_,?_,cf.1.trans (bf.1.trans aa),
    cf.2.2.1.trans (bf.2.2.1.trans am),(af.mono (by decide)).trans (bframe.trans cframe),keep⟩
  · convert ea.seq (eb.seq ec) using 1 <;> first | rfl | omega
  · exact ((tkeep 105 (by decide)).trans (bf.2.2.2.2.2.1 105 (by decide) (by decide))).trans a105
  · rw [tkeep 111 (by decide)]
    simpa [b,Store.ofState,BitTape.blank] using b111
  · simpa [t,Store.ofState,BitTape.shiftedEnd,BitTape.atEnd] using c112

end Maxwell.Cost.SparseEmission.ReadSelector
