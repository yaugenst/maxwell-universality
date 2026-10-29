import Maxwell.Cost.SourceCircuit.ScanBits

namespace Maxwell.Cost.SourceCircuit.SeekEnd
open Structured

def code (source : ℕ) : Code := ScanBits.code source .skip

theorem passive_refl (source : ℕ) (s : Store) : ScanBits.Passive source s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩

theorem passive_trans {source : ℕ} {s t u : Store}
    (h : ScanBits.Passive source s t) (k : ScanBits.Passive source t u) :
    ScanBits.Passive source s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun j hj => (k.tapes j hj).trans (h.tapes j hj),
    fun j hj hk => (k.registers j hj hk).trans (h.registers j hj hk)⟩

theorem executes (source : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted word origin) :
    ∃ cost t, cost ≤ 9*word.length+4 ∧ Executes input tape (code source) cost s t ∧
      t.val.tapes source = BitTape.shiftedEnd word origin ∧ ScanBits.Passive source s t := by
  let invariant : List Bool → Unit → Store → Prop := fun _ _ t => ScanBits.Passive source s t
  obtain ⟨cost,t,hcost,he,hi,ht⟩ := ScanBits.executes source .skip id input tape invariant 1
    (by intro bits data u v hp hi; exact passive_trans hi hp)
    (by intro bits data u hi; exact hi)
    (by intro bits data u hi; exact ⟨1,u,by omega,.skip u,hi,rfl⟩)
    word [] origin () s (by simpa [Increment.cursor,BitTape.shifted] using hs) (passive_refl source s)
  exact ⟨cost,t,by omega,he,by simpa using ht,hi⟩

end Maxwell.Cost.SourceCircuit.SeekEnd
