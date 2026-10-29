import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation
open Control

/-- Replacing the live stack requires only its length and represented
prefix; all other banks and metadata are preserved explicitly. -/
theorem Ready.replace_address {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s t : Store} (h : Ready L origin center bits source s)
    (address : List Bool)
    (keep : ∀ j, j ≠ addressLength → (∀ c, j ≠ L.slot origin 1 c) →
      t.val.indices j = s.val.indices j)
    (hlen : t.val.indices addressLength = address.length)
    (hstack : ∀ j < address.length, t.val.indices (L.slot origin 1 j) =
      (address.reverse[j]?.getD false).toNat)
    (hc : t.val.randomCursor = s.val.randomCursor) :
    Ready L origin center bits {source with address := address} t := by
  have ho : 256 ≤ origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  have low (j : ℕ) (hj : j < origin) (hn : j ≠ addressLength) :
      t.val.indices j = s.val.indices j := by
    apply keep j hn
    intro c
    have := L.slot_ge_origin origin 1 c
    omega
  have small (j : ℕ) (hj : j < 256) (hn : j ≠ addressLength) :
      t.val.indices j = s.val.indices j := low j (by omega) hn
  have bank (b c : ℕ) (hb : b < L.stride) (hne : b ≠ 1) :
      t.val.indices (L.slot origin b c) = s.val.indices (L.slot origin b c) := by
    apply keep
    · have := L.slot_ge_origin origin b c
      unfold addressLength
      omega
    · intro d he
      exact hne ((L.slot_injective origin b 1 c d hb (by simp [Layout.stride])).mp he).1
  refine ⟨{
    origin_above_frame := h.origin_above_frame
    pc := (small _ (by decide) (by decide)).trans h.pc
    address_length := hlen
    input_head := (small _ (by decide) (by decide)).trans h.input_head
    registers := ?_
    tape_heads := ?_
    origin_word := (small _ (by decide) (by decide)).trans h.origin_word
    stride_word := (small _ (by decide) (by decide)).trans h.stride_word
    center_word := (small _ (by decide) (by decide)).trans h.center_word
    input_base := (small _ (by decide) (by decide)).trans h.input_base
    input_length := (small _ (by decide) (by decide)).trans h.input_length
    output_base := (small _ (by decide) (by decide)).trans h.output_base
    output_length := (small _ (by decide) (by decide)).trans h.output_length
    input_cells := fun j hj => (bank L.inputBank j (by simp [Layout.inputBank, Layout.stride])
      (by simp [Layout.inputBank])).trans (h.input_cells j hj)
    output_cells := fun j hj => (bank L.outputBank j (by simp [Layout.outputBank, Layout.stride])
      (by simp [Layout.outputBank])).trans (h.output_cells j hj)
    stack_cells := hstack
    memory_cells := fun a => (bank 0 a L.stride_pos (by decide)).trans (h.memory_cells a)
    tape_cells := fun tape ht z hz => (bank (2 + tape) (centered center z)
      (by simp only [Layout.stride]; omega) (by omega)).trans (h.tape_cells tape ht z hz)
    random_cursor := hc.trans h.random_cursor },
    (small _ (by decide) (by decide)).trans h.zero,
    (small _ (by decide) (by decide)).trans h.one,
    (small _ (by decide) (by decide)).trans h.active⟩
  · intro r hr
    have hro : L.bitRegister r < origin := by
      have := h.origin_above_frame
      unfold Layout.frameEnd Layout.bitRegister at *
      omega
    exact (low _ hro (by unfold Layout.bitRegister addressLength; omega)).trans (h.registers r hr)
  · intro r hr
    have hro : L.tapeHead r < origin := by
      have := h.origin_above_frame
      unfold Layout.frameEnd Layout.tapeHead at *
      omega
    exact (low _ hro (by unfold Layout.tapeHead addressLength; omega)).trans (h.tape_heads r hr)

theorem Ready.push_address {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) (b : Bool) :
    Ready L origin center bits {source with address := b :: source.address}
      ((s.put (L.slot origin 1 source.address.length) b.toNat).put
        addressLength (source.address.length + 1)) := by
  have ho : 256 ≤ origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  apply h.replace_address (b :: source.address)
  · intro j hj hs
    simp only [Store.put_indices, hj, hs source.address.length, ↓reduceIte]
  · simp
  · intro j hj
    have hlow : L.slot origin 1 j ≠ addressLength := by
      have := L.slot_ge_origin origin 1 j
      unfold addressLength
      omega
    simp only [Store.put_indices, hlow, ↓reduceIte]
    by_cases he : j = source.address.length
    · subst j
      simp [List.reverse_cons]
    · have hj' : j < source.address.length := by simp only [List.length_cons] at hj; omega
      have hne : L.slot origin 1 j ≠ L.slot origin 1 source.address.length := by
        intro hh
        exact he ((L.slot_injective origin 1 1 j source.address.length
          (by simp [Layout.stride]) (by simp [Layout.stride])).mp hh).2
      rw [ite_eq_right hne, List.reverse_cons, List.getElem?_append_left (by simpa using hj')]
      exact h.stack_cells j hj'
  · rfl

theorem Ready.shorten_address {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (address : List Bool) (hlen : address.length ≤ source.address.length)
    (hprefix : ∀ j < address.length, address.reverse[j]? = source.address.reverse[j]?) :
    Ready L origin center bits {source with address := address}
      (s.put addressLength address.length) := by
  apply h.replace_address address
  · intro j hj _
    simp only [Store.put_indices, hj, ↓reduceIte]
  · simp
  · intro j hj
    have hlow : L.slot origin 1 j ≠ addressLength := by
      have := h.origin_above_frame
      have := L.slot_ge_origin origin 1 j
      unfold Layout.frameEnd addressLength at *
      omega
    simp only [Store.put_indices, hlow, ↓reduceIte, hprefix j hj]
    exact h.stack_cells j (hj.trans_le hlen)
  · rfl

theorem Ready.pop_address {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) :
    Ready L origin center bits {source with address := source.address.tail}
      (s.put addressLength (source.address.length - 1)) := by
  have ht := h.shorten_address source.address.tail (by simp) (by
    intro j hj
    cases ha : source.address with
    | nil => simp [ha] at hj
    | cons b rest =>
      simp only [ha, List.tail_cons] at hj ⊢
      rw [List.reverse_cons, List.getElem?_append_left (by simpa using hj)])
  simpa only [List.length_tail] using ht

theorem Ready.clear_address {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) :
    Ready L origin center bits {source with address := []} (s.put addressLength 0) :=
  h.shorten_address [] (by simp) (by simp)

theorem reverse_top (address : List Bool) (h : address ≠ []) :
    (address.reverse[address.length - 1]?.getD false) = address.headD false := by
  cases address with
  | nil => exact (h rfl).elim
  | cons b rest => simp [List.reverse_cons]

end Maxwell.Cost.RealSimulation
