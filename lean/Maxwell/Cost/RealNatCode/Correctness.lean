import Maxwell.Cost.RealNatCode.Payload

namespace Maxwell.Cost.RealNatCode
open RealSparse (execute execute_sound)

/-- The actual canonical codec resides in the caller's index-memory buffer. -/
def Stored (s : RAMState) (L : Layout) (n : ℕ) : Prop :=
  ∀ j < (Codec.nat n).length,
    s.indices (L.bufferAt j) = ((Codec.nat n)[j]?.getD false).toNat

theorem payloadReady_stored (s : RAMState) (L : Layout) (n : ℕ)
    (h : PayloadReady s L n 0) : Stored s L n := by
  intro j hj
  rw [code_get n j hj]
  by_cases hlt : j < n.size
  · simpa [hlt] using h.header j hlt
  · by_cases heq : j = n.size
    · subst j
      simpa using h.separator
    · have hk : j - n.size - 1 < n.size := by
        rw [code_length] at hj
        omega
      have hj' : n.size + 1 + (j - n.size - 1) = j := by omega
      simpa [hlt, heq, hj'] using h.payload (j - n.size - 1) (by omega) hk

/-- Full finite-code serialization, from arbitrary caller state and actual
runtime arguments. The cache has a separate bank and may contain old data. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (hpc : s.pc = 0) (hn : s.indices 2 = n)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hd : s.indices 22 = L.stride) :
    ∃ t : RAMState, Terminates (program.next input tape) (23 * n.size + 13) s t ∧
      t.pc = 36 ∧ t.indices 7 = n.size ∧ Stored t L n := by
  have hi := execute_sound _ (initialize_steps input tape s hpc)
  obtain ⟨s₁, h₁, hr₁⟩ := powers input tape L n n.size (initialized s) 0
    (initialized_ready s L n hpc hn hc hb hd) (by omega)
  have hb₁ := execute_sound _ (header_start_steps input tape L n s₁ hr₁)
  obtain ⟨s₂, h₂, hr₂⟩ := headers input tape L n n.size (headerStart s₁) 0
    (headerStart_ready L n s₁ hr₁) (by omega)
  have hb₂ := execute_sound _ (payload_start_steps input tape L n s₂ hr₂)
  obtain ⟨s₃, h₃, hr₃⟩ := payloads input tape L n n.size (payloadStart s₂)
    (payloadStart_ready L n s₂ hr₂) (by omega)
  let t : RAMState := {s₃ with pc := 36}
  have he : Steps (program.next input tape) 1 s₃ t := by
    apply execute_sound
    simp [execute, program, Machine.next, t, hr₃.pc, hr₃.count, hr₃.zero]
  refine ⟨t, ?_, rfl, hr₃.length, payloadReady_stored s₃ L n hr₃⟩
  convert ((((((hi.trans h₁).trans hb₁).trans h₂).trans hb₂).trans h₃).trans he).terminates
    (Terminates.halt t (by simp [program, Machine.next, t])) using 1
  omega

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (hpc : s.pc = 0) (hn : s.indices 2 = n)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hd : s.indices 22 = L.stride) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (23 * n.size + 14) s).finished = some t ∧
      (runCapped (program.next input tape) (23 * n.size + 14) s).instructions = 23 * n.size + 13 ∧
      t.indices 7 = n.size ∧ Stored t L n := by
  obtain ⟨t, ht, _, hl, hs⟩ := terminates input tape L n s hpc hn hc hb hd
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates _ ht
  exact ⟨t, hf, hcost, hl, hs⟩

end Maxwell.Cost.RealNatCode
