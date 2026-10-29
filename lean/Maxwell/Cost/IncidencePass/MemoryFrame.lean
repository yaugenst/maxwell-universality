import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.IncidencePass

/-- Only the two-bit counter and rank intervals are mutated. -/
def Outside (layout : IncidenceEncoding.Layout) (vertices incidences address : ℕ) : Prop :=
  (address<layout.baseCounter ∨ layout.baseCounter+vertices*2≤address) ∧
  (address<layout.baseRank ∨ layout.baseRank+incidences*2≤address)

def MemoryFrame (layout : IncidenceEncoding.Layout) (vertices incidences : ℕ)
    (before after : ℕ → Bool) : Prop :=
  ∀ address, Outside layout vertices incidences address → after address=before address

theorem MemoryFrame.refl (layout : IncidenceEncoding.Layout) (v i : ℕ) (memory : ℕ → Bool) :
    MemoryFrame layout v i memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {layout : IncidenceEncoding.Layout} {v i : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout v i a b) (j : MemoryFrame layout v i b c) : MemoryFrame layout v i a c :=
  fun p hp => (j p hp).trans (h p hp)

theorem MemoryFrame.of_eq {layout : IncidenceEncoding.Layout} {v i : ℕ} {a b : ℕ → Bool}
    (h : b=a) : MemoryFrame layout v i a b := fun p _ => congrFun h p

theorem stepMemory_frame {v i : ℕ} (layout : IncidenceEncoding.Layout)
    (endpoint : Fin i → Fin v) (index : Fin i) (saved : Maxwell.Logical.Routing.IncidenceRanks.State v i)
    (memory : ℕ → Bool) : MemoryFrame layout v i memory (IncidenceEncoding.stepMemory layout endpoint index saved memory) := by
  intro p hp
  have hv := (endpoint index).isLt
  have hi := index.isLt
  unfold IncidenceEncoding.stepMemory
  rw [MemoryWord.writeBits_outside,MemoryWord.writeBits_outside]
  · simp only [IncidenceEncoding.word_length]
    rcases hp.1 with h | h <;> omega
  · simp only [IncidenceEncoding.word_length]
    rcases hp.2 with h | h <;> omega

/-- A later packed array (in particular the graph diagonal) is retained. -/
theorem MemoryFrame.represents_after {layout : IncidenceEncoding.Layout} {v i n base width : ℕ}
    {before after : ℕ → Bool} {values : Vector (List Bool) n}
    (h : MemoryFrame layout v i before after)
    (hc : layout.baseCounter+v*2≤base) (hr : layout.baseRank+i*2≤base)
    (harray : BitArray.Represents before base width values) :
    BitArray.Represents after base width values := by
  refine ⟨harray.length,?_⟩
  intro index bit hbit
  rw [h _ ⟨Or.inr (by omega),Or.inr (by omega)⟩]
  exact harray.bits index bit hbit

end Maxwell.Cost.IncidencePass
