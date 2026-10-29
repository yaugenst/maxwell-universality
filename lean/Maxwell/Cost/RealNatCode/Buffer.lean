import Maxwell.Cost.RealNatCode.Frame

namespace Maxwell.Cost.RealNatCode

/-- Appending starts a new codec interval in the same physical bit bank. -/
def Layout.shiftBuffer (L : Layout) (offset : ℕ) : Layout where
  cache := L.cache
  buffer := L.bufferAt offset
  stride := L.stride
  cache_ge := L.cache_ge
  buffer_ge := L.bufferAt_ge offset
  stride_pos := L.stride_pos
  disjoint i j := by
    have h := L.disjoint i (offset + j)
    simpa [Layout.bufferAt, Nat.mul_add, Nat.add_assoc] using h

@[simp] theorem Layout.shiftBuffer_cacheAt (L : Layout) (offset j : ℕ) :
    (L.shiftBuffer offset).cacheAt j = L.cacheAt j := rfl

@[simp] theorem Layout.shiftBuffer_bufferAt (L : Layout) (offset j : ℕ) :
    (L.shiftBuffer offset).bufferAt j = L.bufferAt (offset + j) := by
  simp [Layout.shiftBuffer, Layout.bufferAt, Nat.mul_add, Nat.add_assoc]

theorem shiftBuffer_protected_prefix (L : Layout) (offset n j : ℕ) (hj : j < offset) :
    Protected (L.shiftBuffer offset) n (L.bufferAt j) := by
  refine ⟨by have := L.bufferAt_ge j; omega, ?_, ?_⟩
  · intro i _
    exact (L.disjoint i j).symm
  · intro i _
    rw [Layout.shiftBuffer_bufferAt]
    intro he
    have := L.bufferAt_injective he
    omega

def StoredWord (s : RAMState) (L : Layout) (bits : List Bool) : Prop :=
  ∀ j < bits.length, s.indices (L.bufferAt j) = (bits[j]?.getD false).toNat

theorem storedWord_append (s : RAMState) (L : Layout) (left right : List Bool)
    (hl : StoredWord s L left) (hr : StoredWord s (L.shiftBuffer left.length) right) :
    StoredWord s L (left ++ right) := by
  intro j hj
  by_cases hlt : j < left.length
  · simpa [List.getElem?_append, hlt] using hl j hlt
  · have hrj : j - left.length < right.length := by
      rw [List.length_append] at hj
      omega
    have he := hr (j - left.length) hrj
    simpa [List.getElem?_append, hlt, Layout.shiftBuffer_bufferAt,
      Nat.add_sub_of_le (by omega : left.length ≤ j)] using he

theorem Frame.preserves_prefix {L : Layout} {offset n : ℕ} {s t : RAMState}
    (h : Frame (L.shiftBuffer offset) n s t) (bits : List Bool)
    (hlen : bits.length ≤ offset) (hs : StoredWord s L bits) : StoredWord t L bits := by
  intro j hj
  exact (h.indices (L.bufferAt j) (shiftBuffer_protected_prefix L offset n j (by omega))).trans (hs j hj)

end Maxwell.Cost.RealNatCode
